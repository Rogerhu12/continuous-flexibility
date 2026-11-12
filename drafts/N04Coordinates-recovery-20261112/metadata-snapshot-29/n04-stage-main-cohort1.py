import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
C9 = 'c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
MFPATH = ROOT / 'n04-drafts/positive/upstream-main-c9/MainC9MinimalContractCohortCI156Pending.json'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def ident(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

def verify(rec):
    actual = ident(rec['path'])
    for key in ('sha256', 'blob', 'lines'):
        if key in rec:
            assert actual[key] == rec[key], (rec['path'], key)
    return Path(rec['path']).read_bytes()

assert ident(MFPATH)['sha256'] == 'b6a815ac93fe5562cfd8df7838590be35e522d9036a3827fc5811bf65dc46437'
proposal = json.loads(MFPATH.read_text())
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
base = git('rev-parse', 'HEAD').decode().strip()
base_tree = git('rev-parse', 'HEAD^{tree}').decode().strip()
main = git('rev-parse', 'origin/main').decode().strip()
assert cp['last_full_green']['sha'] == base, 'Complete current-head CI is required before main source activation'
assert cp['current_ci']['head'] == base and cp['current_ci']['status'] == 'success'
assert not git('status', '--porcelain')
assert not git('diff', C9, main, '--', 'src', 'scripts/gen_root.py', 'scripts/root_exclude.txt', 'AGENTS.md', 'docs/tasks/README.md')
assert (REPO / '.github/workflows/build.yml').read_bytes() == git('show', main + ':.github/workflows/build.yml')
label = cp['current_ci']['label'] + 1
batch = proposal['batch']
assert batch['module_count'] == 32
verify(proposal['parent_proposal'])
owners = []
for item in proposal['local_port_owner_manifests']:
    obj = json.loads(verify(item))
    assert 'REVIEW' in str(obj.get('status', '')).upper(), item['path']
    owners.append(item)
selected = []
new_count = 0
for row in batch['modules_in_dependency_order']:
    target = row['target_path']
    p = REPO / target
    pre = row['preimage']
    if pre is None:
        assert not p.exists(), target
        new_count += 1
    else:
        before = ident(p)
        assert before['blob'] == pre['blob'] and before['sha256'] == pre['sha256'], target
        assert p.read_bytes() == git('show', base + ':' + target)
    if row.get('source_path'):
        raw = Path(row['source_path']).read_bytes()
    else:
        assert row['source_ref'] == C9
        raw = git('show', C9 + ':' + target)
    assert hashlib.sha256(raw).hexdigest() == row['sha256'], target
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['blob'], target
    assert len(raw.decode().splitlines()) == row['lines'], target
    selected.append((row, raw))
assert new_count == 3
protected = 'src/ContinuousFlexibility/Analysis/CanonicalPositiveSourceJetBounds.lean'
protected_bytes = (REPO / protected).read_bytes()
for row, raw in selected:
    p = REPO / row['target_path']
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(raw)
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
rootfile = REPO / 'src/ContinuousFlexibility.lean'
assert ident(rootfile)['blob'] == batch['generated_root_projection']['blob']
assert (REPO / protected).read_bytes() == protected_bytes
assert git('rev-parse', 'HEAD:src/ContinuousFlexibility/Blueprint/Statements.lean').decode().strip() == proposal['first_batch_exception']['retained_blob']
paths = sorted([row['target_path'] for row, _ in selected] + ['src/ContinuousFlexibility.lean'])
git('add', '--', *paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert not git('diff')
assert git('diff', '--cached', '--name-only').decode().splitlines() == paths
tree = git('write-tree').decode().strip()
numstat = git('diff', '--numstat', base, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in numstat)
deleted = sum(int(x.split()[1]) for x in numstat)
assert added == batch['added_Lean_lines_including_generated_root_and_extras'] == 966
assert deleted == batch['deleted_Lean_lines'] == 306
assert added <= 20000
module_paths = {str(p.relative_to(REPO / 'src')).removesuffix('.lean').replace('/', '.')
                for p in (REPO / 'src').rglob('*.lean')}
missing = []
for p in (REPO / 'src').rglob('*.lean'):
    for imp in re.findall(r'^import\s+(\S+)', p.read_text(), re.M):
        if imp.startswith('ContinuousFlexibility.') and imp not in module_paths:
            missing.append([str(p), imp])
assert not missing, missing
plan = {
    'label': label, 'head_before': base, 'base_tree': base_tree, 'tree': tree,
    'main_checked': main, 'main_integrated': cp['current_ci']['main'],
    'main_source_batch': 1, 'main_source_batch_count': 5,
    'last_full_green': base, 'green_receipt': cp['last_full_green'],
    'source_proposal': ident(MFPATH), 'local_owner_manifests': owners,
    'sources': [row for row, _ in selected], 'paths': paths,
    'additional_parents': [],
    'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
    'source_total': len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
    'source_all_total': len(list((REPO / 'src').rglob('*.lean'))),
    'root_imports': sum(x.startswith('import ') for x in rootfile.read_text().splitlines()),
    'scope': 'First atomic current-main source cohort: new parameter-order flow contract with all identified active consumers, exact upstream restriction providers and independently reviewed local ports. The stronger N01a/N01b blueprint witness and factories remain together in batch two. No main ancestry claim yet; next batch requires complete CI.',
    'created_at': datetime.now(timezone.utc).isoformat()
}
(ROOT / f'n04-ci{label}-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()} for p in paths]
text = json.dumps(payload, ensure_ascii=False)
(ROOT / f'n04-ci{label}-tree-payload.json').write_text(text)
print(json.dumps({'label': label, 'tree': tree, 'paths': len(paths),
    'added_lean_since_full_green': added, 'payload_codepoints': len(text),
    'payload_sha256': hashlib.sha256(text.encode()).hexdigest()}))
