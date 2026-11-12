import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
selection_path = Path(sys.argv[1])
selection_sha = sys.argv[2]

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def fp(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.splitlines())}

def verify(row):
    actual = fp(row['path'])
    for key in ('sha256', 'blob', 'lines'):
        if key in row:
            assert actual[key] == row[key], (row['path'], key)

assert fp(selection_path)['sha256'] == selection_sha
selection = json.loads(selection_path.read_text())
assert selection['status'] == 'FULL_SOURCE_PEER_PASSED_HELD_UNCOMPILED'
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
cur = cp['current_ci']
assert cur['status'] == 'success' and cur['label'] == selection['required_full_green_ci']
assert cp['last_full_green']['sha'] == cur['head'] == selection['baseline_head']
assert git('rev-parse', 'HEAD').decode().strip() == selection['baseline_head']
assert git('rev-parse', 'origin/main').decode().strip() == selection['main_pin']
label = cur['label'] + 1
plan_path = ROOT / f'n04-ci{label}-plan.json'
plan = json.loads(plan_path.read_text())
assert plan['head_before'] == cur['head'] and plan['main_source_batch'] == selection['target_batch']
assert plan['main_checked'] == selection['main_pin']
assert plan['tree'] == git('write-tree').decode().strip()
assert not git('diff') and not git('ls-files', '--others', '--exclude-standard')
assert git('diff', '--cached', '--name-only').decode().splitlines() == plan['paths']
for evidence in selection['review_evidence']:
    verify(evidence)
selected = {row['module']: row for row in selection['sources']}
assert len(selected) == len(selection['sources'])
for module, row in selected.items():
    verify(row)
    assert row['target_path'] == 'src/' + module.replace('.', '/') + '.lean'
    assert not (REPO / row['target_path']).exists()
    source = Path(row['path']).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)', source)
    for name in re.findall(r'^(?:theorem|def|abbrev)\s+(\S+)', source, re.M):
        result = subprocess.run(['git', 'grep', '-n', '-E',
            r'^(theorem|def|abbrev|lemma|structure|inductive) ' + re.escape(name) + r'([ :({]|$)',
            cur['head'], '--', 'src'], cwd=REPO, capture_output=True)
        assert result.returncode == 1, (name, result.stdout.decode())
covered = set()
for graph_record in selection['selected_provider_graphs']:
    verify(graph_record)
    graph = json.loads(Path(graph_record['path']).read_text())
    nodes = graph['nodes']
    assert not graph.get('missing') and not graph.get('cycles')
    for module, row in nodes.items():
        actual_path = Path(selected[module]['path']) if module in selected else REPO / ('src/' + module.replace('.', '/') + '.lean')
        actual = fp(actual_path)
        assert actual['sha256'] == row['sha256'] and actual['blob'] == row['blob'], ('provider_mismatch', module)
        assert re.findall(r'^import\s+(\S+)', actual_path.read_text(), re.M) == row['imports'], module
        assert all(not imp.startswith('ContinuousFlexibility.') or imp in nodes for imp in row['imports']), module
        if module in selected:
            covered.add(module)
assert covered == set(selected)
assert sum(row['lines'] for row in selected.values()) == selection['source_lines']
base_plan_bytes = plan_path.read_bytes()
base_payload_path = ROOT / f'n04-ci{label}-tree-payload.json'
base_payload_bytes = base_payload_path.read_bytes()
for row in selected.values():
    (REPO / row['target_path']).write_bytes(Path(row['path']).read_bytes())
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
paths = sorted(set(plan['paths']) | {row['target_path'] for row in selected.values()})
git('add', '--', *paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert not git('diff') and not git('ls-files', '--others', '--exclude-standard')
assert git('diff', '--cached', '--name-only').decode().splitlines() == paths
tree = git('write-tree').decode().strip()
stats = git('diff', '--numstat', '--no-renames', cur['head'], tree, '--', '*.lean').decode().splitlines()
added = sum(int(row.split()[0]) for row in stats)
deleted = sum(int(row.split()[1]) for row in stats)
assert added == plan['added_lean_since_full_green'] + selection['source_lines'] + len(selected)
assert deleted == plan['deleted_lean_since_full_green'] and added <= 20000
graph = {}
for path in (REPO / 'src').rglob('*.lean'):
    module = str(path.relative_to(REPO / 'src')).removesuffix('.lean').replace('/', '.')
    graph[module] = [imp for imp in re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
                     if imp.startswith('ContinuousFlexibility.')]
visiting, done = set(), set()
def visit(module):
    if module in done:
        return
    assert module in graph and module not in visiting, ('missing_or_cycle', module)
    visiting.add(module)
    for imp in graph[module]:
        visit(imp)
    visiting.remove(module)
    done.add(module)
for module in graph:
    visit(module)
saved_plan = ROOT / f'n04-ci{label}-plan-main-only.json'
saved_payload = ROOT / f'n04-ci{label}-tree-payload-main-only.json'
assert not saved_plan.exists() and not saved_payload.exists()
saved_plan.write_bytes(base_plan_bytes)
saved_payload.write_bytes(base_payload_bytes)
plan.update(tree=tree, paths=paths, added_lean_since_full_green=added,
    deleted_lean_since_full_green=deleted,
    source_total=len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
    source_all_total=len(list((REPO / 'src').rglob('*.lean'))),
    root_imports=sum(line.startswith('import ') for line in (REPO / 'src/ContinuousFlexibility.lean').read_text().splitlines()),
    main_only_plan=fp(saved_plan), independent_coordinate_leaf_selection=fp(selection_path),
    independent_coordinate_leaf_count=len(selected), independent_coordinate_leaf_lines=selection['source_lines'],
    finalized_at=datetime.now(timezone.utc).isoformat())
plan['sources'].extend(dict(row, source_path=row['path'], source_ref='REVIEWED_LOCAL_CANDIDATE') for row in selected.values())
plan['scope'] += f' Also activate {len(selected)} independently reviewed coordinate leaves ({selection["source_lines"]} source lines); every selected provider was rechecked against this exact projected tree.'
plan_path.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
payload = json.dumps([{'path': path, 'mode': '100644', 'type': 'blob',
                      'content': (REPO / path).read_text()} for path in paths], ensure_ascii=False)
base_payload_path.write_text(payload)
print(json.dumps({'label': label, 'tree': tree, 'paths': len(paths), 'added_lean': added,
    'deleted_lean': deleted, 'coordinate_modules': len(selected),
    'payload_codepoints': len(payload), 'payload_sha256': hashlib.sha256(payload.encode()).hexdigest()}))
