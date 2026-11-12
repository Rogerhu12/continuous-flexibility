import hashlib, json, re, subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
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
    for k in ('sha256', 'blob', 'lines'):
        if k in row:
            assert actual[k] == row[k], (row['path'], k)
    return Path(row['path']).read_bytes()

cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
base = git('rev-parse', 'HEAD').decode().strip()
assert base == cp['head'] == '7ac330b2e0c2420e449235a090055a8018ebf17e'
assert cp['current_ci']['label'] == 161 and cp['current_ci']['status'] == 'failure'
assert cp['current_ci']['main_source_batch'] == 1
assert not git('status', '--porcelain')
main = git('rev-parse', 'origin/main').decode().strip()
assert main == '2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d'
configs = [
    ('positive/repair161/N01NeighborhoodRestrictionCI161RepairReviewedManifest.json',
     '4dba1684f7f844118ee9b5f0b3d51ec3473a40a02a371f441eb664aa997bae11',
     'src/ContinuousFlexibility/Analysis/N01NeighborhoodRestriction.lean'),
    ('quantitative/repair161/N01ControlFlowBoundsCI161RepairReviewedManifest.json',
     '72600908b06e4d4e4959e159730b8da4f58544509031d25a1497412c21b58337',
     'src/ContinuousFlexibility/Analysis/N01ControlFlowBounds.lean')]
selected, owners, peers = [], [], []
for rel, expected, target in configs:
    path = ROOT / 'n04-drafts' / rel
    assert fp(path)['sha256'] == expected
    owner = json.loads(path.read_text())
    raw = verify(owner['source'])
    candidate = json.loads(verify(owner['candidate_manifest']))
    base_row = candidate.get('base') or candidate['preimage']
    base_raw = verify(base_row)
    assert base_raw == (REPO / target).read_bytes() == git('show', base + ':' + target)
    review_rows = owner.get('independent_reviews', [owner.get('independent_review')])
    for row in review_rows:
        peer = json.loads(verify(row))
        assert peer['source'] == owner['source']
        assert peer['compiled'] is False
        peers.append(row)
    assert not re.search(rb'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)', raw)
    owners.append(fp(path))
    selected.append((target, raw, owner['source'], base_row))
root_before = (REPO / 'src/ContinuousFlexibility.lean').read_bytes()
for target, raw, _, _ in selected:
    (REPO / target).write_bytes(raw)
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
assert (REPO / 'src/ContinuousFlexibility.lean').read_bytes() == root_before
targets = [x[0] for x in selected]
assert set(git('diff', '--name-only').decode().splitlines()) == set(targets)
git('diff', '--check')
git('add', '--', *targets)
tree = git('write-tree').decode().strip()
stats = git('diff', '--cached', '--numstat', '--no-renames', cp['last_full_green']['sha'], '--', '*.lean').decode().splitlines()
added = sum(int(line.split('\t')[0]) for line in stats)
deleted = sum(int(line.split('\t')[1]) for line in stats)
assert added <= 20000
for path in ('CanonicalPositiveSourceJetBounds.lean', 'CanonicalPositiveSourcePrefixBounds.lean'):
    target = 'src/ContinuousFlexibility/Analysis/' + path
    assert (REPO / target).read_bytes() == git('show', cp['last_full_green']['sha'] + ':' + target)
payload = [{'path': target, 'mode': '100644', 'type': 'blob', 'content': raw.decode()} for target, raw, _, _ in selected]
(ROOT / 'n04-ci162-tree-payload.json').write_text(json.dumps(payload, ensure_ascii=False))
plan = {
    'label': 162, 'head_before': base, 'base_tree': cp['tree'], 'tree': tree,
    'main_checked': main, 'main_integrated': cp['current_ci']['main'],
    'main_source_batch': 1, 'main_source_batch_count': 5,
    'last_full_green': cp['last_full_green']['sha'], 'owner_manifests': owners,
    'independent_reviews': peers,
    'sources': [dict(target=target, source=source, preimage=preimage) for target, _, source, preimage in selected],
    'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
    'source_total': len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
    'source_all_total': len(list((REPO / 'src').rglob('*.lean'))),
    'root_imports': len(re.findall(r'^import ', root_before.decode(), re.M)),
    'scope': 'Repair only the exact two CI161 diagnostics: typed per-k choice projections for the neighborhood helper and explicit scalar endpoint arguments for the optical helper. Every other source byte, public contract and default resource setting is preserved. Current-main source batch remains 1/5; further cohorts require full CI.',
    'created_at': datetime.now(timezone.utc).isoformat()}
(ROOT / 'n04-ci162-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({k: plan[k] for k in ('label','head_before','tree','source_total','source_all_total','root_imports','added_lean_since_full_green','deleted_lean_since_full_green')}))
