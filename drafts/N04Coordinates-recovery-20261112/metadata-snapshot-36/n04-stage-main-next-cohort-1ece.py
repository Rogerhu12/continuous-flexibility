import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
C9 = 'c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
MFPATH = ROOT / 'n04-drafts/positive/upstream-main-c9/MainC9BoundedIntegrationBatchProposalCI155.json'
BATCH = int(sys.argv[1])
assert 3 <= BATCH <= 5
MAIN_PIN = '1ecee654ecfa9cf39b8d846dccbf593ec1c0f2ac'
EQPATH = ROOT / 'n04-drafts/quantitative/recovery/Batch2To5SourceEqualityAtMain1ece.json'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def raw_ident(raw):
    return {'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

def ident(path):
    path = Path(path)
    return dict(path=str(path), **raw_ident(path.read_bytes()))

def verify(rec):
    raw = Path(rec['path']).read_bytes()
    actual = raw_ident(raw)
    for key in ('sha256', 'blob', 'lines'):
        if key in rec:
            assert actual[key] == rec[key], (rec['path'], key)
    return raw

assert ident(MFPATH)['sha256'] == '3d4897a11c85b1601f624161a61d38f1633aff3a388ff1fdc90812aec9e757c1'
proposal = json.loads(MFPATH.read_text())
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
cur = cp['current_ci']
base = git('rev-parse', 'HEAD').decode().strip()
base_tree = git('rev-parse', 'HEAD^{tree}').decode().strip()
main = git('rev-parse', 'origin/main').decode().strip()
assert cp['last_full_green']['sha'] == base, 'Complete current-head CI is required'
assert cur['head'] == base and cur['status'] == 'success'
assert cur['main_source_batch'] == BATCH - 1, 'Previous atomic cohort must be complete'
assert not git('status', '--porcelain')
assert main == MAIN_PIN, 'Re-audit new main before staging a cohort.'
assert ident(EQPATH)['sha256'] == 'e180ff4b0292124aade3ea84b6a48231abecbe97f86a49b99f9d34e43158b286'
equality = json.loads(EQPATH.read_text())
assert equality['refs']['fixed_new_main'] == main and equality['refs']['old_plan_main_Lean'] == C9
assert equality['inputs']['original_proposal']['sha256'] == ident(MFPATH)['sha256']
assert equality['summary']['batches_3_to_5_exact_upstream_equal'] == 367
assert not git('diff', C9, main, '--', 'scripts/gen_root.py', 'scripts/root_exclude.txt',
               'AGENTS.md', 'docs/tasks/README.md', 'docs/tasks/N04Coordinates.md',
               'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
for control in equality['rules_workflow_and_toolchain']:
    assert (REPO / control['path']).read_bytes() == git('show', main + ':' + control['path'])
assert (REPO / '.github/workflows/build.yml').read_bytes() == git('show', main + ':.github/workflows/build.yml')
batch = proposal['batches'][BATCH - 1]
assert batch['number'] == BATCH and not batch['missing_imports']
assert not batch['introduced_public_name_repetitions'] and not batch['parser_warnings']
owners = []
if BATCH == 2:
    verify(proposal['later_common_provider_candidate'])
    owner_path = ROOT / 'n04-drafts/positive/compatibility/main-c9-mixed-provider/LocalMixedCommonProviderReviewedManifest.json'
    owner = json.loads(owner_path.read_text())
    assert owner['status'] == 'FULL_SOURCE_PEER_PASSED_HELD_UNCOMPILED_PROVIDER_ATOMIC_PAIR_ONLY'
    assert owner['candidate']['sha256'] == proposal['later_common_provider_candidate']['sha256']
    for key in ('candidate', 'independent_review', 'source', 'base', 'selected_provider'):
        verify(owner[key])
    assert owner['independent_review']['sha256'] == '62947e45ef1133a7036ff9bb9e738f3c8538264f61fc6e6ed7912a8515e8a13d'
    provider = next(row for row in batch['modules_in_dependency_order']
                    if row['module'] == 'ContinuousFlexibility.Analysis.N01cSpatialParameterComposition')
    assert provider['blob'] == owner['selected_provider']['blob']
    owners.append(ident(owner_path))
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
        actual = ident(p)
        assert actual['blob'] == pre['blob'] and actual['sha256'] == pre['sha256'], target
        assert p.read_bytes() == git('show', base + ':' + target)
    if row.get('source_path'):
        assert BATCH == 2 and row['module'] == 'ContinuousFlexibility.Analysis.LocalMixedProductBounds'
        raw = Path(row['source_path']).read_bytes()
        assert row['blob'] == owner['source']['blob']
    else:
        assert row['source_ref'] == C9
        raw = git('show', C9 + ':' + target)
        assert raw == git('show', main + ':' + target), ('cohort_source_changed_on_main', target)
    actual = raw_ident(raw)
    for key in ('sha256', 'blob', 'lines'):
        assert actual[key] == row[key], (target, key)
    selected.append((row, raw))
assert new_count == batch['new_modules']
extras = []
for row in batch['other_Lean_files']:
    assert BATCH == 5 and row['source_ref'] == C9
    target = row['target_path']
    p = REPO / target
    if row['old_blob'] is None:
        assert not p.exists(), target
    else:
        assert ident(p)['blob'] == row['old_blob'], target
        assert p.read_bytes() == git('show', base + ':' + target)
    raw = git('show', C9 + ':' + target)
    if target == 'scripts/BlueprintStatus.lean':
        # Keep the frozen c9 audit until the later N02N03 integration cohort.
        assert raw_ident(raw)['blob'] == 'eeb271fc511451b1de49f2d411ddb77a8a8269f1'
        newest = git('show', main + ':' + target)
        assert raw_ident(newest)['blob'] == 'fb801d69e8ffce22cab163bfbfa653d755d58cc4'
        assert newest == raw + b'\n#print axioms ContinuousFlexibility.Blueprint.N02N03\n'
    else:
        assert raw == git('show', main + ':' + target), ('extra_source_changed_on_main', target)
    actual = raw_ident(raw)
    for key in ('sha256', 'blob', 'lines'):
        assert actual[key] == row[key], (target, key)
    extras.append((row, raw))
protected = {p: (REPO / p).read_bytes() for p in [
    'src/ContinuousFlexibility/Analysis/CanonicalPositiveSourceJetBounds.lean',
    'src/ContinuousFlexibility/Analysis/CanonicalPositiveSourcePrefixBounds.lean']}
for row, raw in selected + extras:
    p = REPO / row['target_path']
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(raw)
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
rootfile = REPO / 'src/ContinuousFlexibility.lean'
assert ident(rootfile)['blob'] == batch['generated_root_projection']['blob']
for path, raw in protected.items():
    assert (REPO / path).read_bytes() == raw
paths = sorted([row['target_path'] for row, _ in selected + extras] + ['src/ContinuousFlexibility.lean'])
git('add', '--', *paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert not git('diff')
assert git('diff', '--cached', '--name-only').decode().splitlines() == paths
tree = git('write-tree').decode().strip()
stats = git('diff', '--numstat', '--no-renames', base, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in stats)
deleted = sum(int(x.split()[1]) for x in stats)
assert added == batch['added_Lean_lines_including_generated_root_and_extras']
assert deleted == batch['deleted_Lean_lines']
assert added <= 17000 <= 20000
graph = {}
for p in (REPO / 'src').rglob('*.lean'):
    name = str(p.relative_to(REPO / 'src')).removesuffix('.lean').replace('/', '.')
    graph[name] = [m for m in re.findall(r'^import\s+(\S+)', p.read_text(), re.M)
                   if m.startswith('ContinuousFlexibility.')]
missing = [(m, d) for m, ds in graph.items() for d in ds if d not in graph]
assert not missing, missing
visiting, done = set(), set()
def visit(m):
    if m in done:
        return
    assert m not in visiting, ('import_cycle', m)
    visiting.add(m)
    for d in graph[m]:
        visit(d)
    visiting.remove(m)
    done.add(m)
for m in graph:
    visit(m)
label = cur['label'] + 1
plan = {
    'label': label, 'head_before': base, 'base_tree': base_tree, 'tree': tree,
    'main_checked': main, 'main_integrated': cur['main'],
    'main_workflow_file_integrated': cur['main_workflow_file_integrated'],
    'main_source_batch': BATCH, 'main_source_batch_count': 5,
    'last_full_green': base, 'green_receipt': cp['last_full_green'],
    'source_proposal': ident(MFPATH), 'local_owner_manifests': owners,
    'new_main_source_equality_review': ident(EQPATH),
    'source_identity_scope': 'All mathematical modules in this retained c9 cohort are byte-identical to main 1ece; the c9 BlueprintStatus extra remains explicitly selected until the later N02N03 cohort. Full current-main integration is still pending.',
    'sources': [row for row, _ in selected], 'other_Lean_files': [row for row, _ in extras],
    'paths': paths, 'additional_parents': [],
    'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
    'line_count_method': 'git diff --numstat --no-renames against the exact complete-green parent',
    'source_total': len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
    'source_all_total': len(list((REPO / 'src').rglob('*.lean'))),
    'root_imports': sum(x.startswith('import ') for x in rootfile.read_text().splitlines()),
    'scope': f'Retained c9 source cohort {BATCH}/5, checked against current main 1ece: {batch["name"]}. Exact upstream sources with the independently reviewed common-provider port where applicable. All preimages and full import graph revalidated; no main ancestry claim yet. Complete CI is required before further activation.',
    'created_at': datetime.now(timezone.utc).isoformat()
}
assert not (ROOT / f'n04-ci{label}-plan.json').exists()
(ROOT / f'n04-ci{label}-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
payload = json.dumps([{'path': p, 'mode': '100644', 'type': 'blob',
                      'content': (REPO / p).read_text()} for p in paths], ensure_ascii=False)
(ROOT / f'n04-ci{label}-tree-payload.json').write_text(payload)
print(json.dumps({'label': label, 'cohort': BATCH, 'tree': tree, 'paths': len(paths),
                  'added_lean': added, 'deleted_lean': deleted,
                  'payload_codepoints': len(payload),
                  'payload_sha256': hashlib.sha256(payload.encode()).hexdigest()}))
