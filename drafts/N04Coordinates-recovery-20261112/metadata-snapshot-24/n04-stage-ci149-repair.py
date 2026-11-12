import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = 'dc2dd491aa653712df6f739448eed9bb1505166e'
BASE_TREE = 'a8d543032b3ba21097e13c34d899fd134443e3a3'
MAIN = 'c070da70d8df06e5345ff10f63aeff17207f257e'
GREEN = '03e526021c371413f03fc0ce052476b63e105361'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(item):
    data = Path(item['path']).read_bytes()
    assert digest(data) == item['sha256'], item['path']
    if 'blob' in item:
        assert git('hash-object', item['path']).decode().strip() == item['blob']
    if 'lines' in item:
        assert len(data.splitlines()) == item['lines']
    return data

assert git('rev-parse', 'HEAD').decode().strip() == BASE
assert git('rev-parse', 'HEAD^{tree}').decode().strip() == BASE_TREE
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
assert not git('status', '--porcelain')
assert subprocess.run(['git', 'merge-base', '--is-ancestor', MAIN, BASE], cwd=REPO).returncode == 0
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert cp['current_ci']['label'] == 148 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
owner_path = ROOT / 'n04-drafts/audit/repair148/N03RootEndpointPhysicalJetsRepairReviewedManifest.json'
owner_bytes = owner_path.read_bytes()
assert digest(owner_bytes) == '111af1bcb05073b5e22c26aa1b344f4f8b9c1ab186dcba7d79319099ddb3e105'
owner = json.loads(owner_bytes)
candidate = json.loads(verify(owner['candidate_manifest']))
for key in ['base_source', 'candidate_source', 'diff', 'surface_comparison', 'independent_review']:
    verify(owner[key])
for item in candidate['read_providers']:
    verify(item)
verify(candidate['cached_log'])
assert owner['actual_base_commit'] == BASE and owner['actual_base_tree'] == BASE_TREE
path = owner['target_path']
assert path == 'src/ContinuousFlexibility/Analysis/N03RootEndpointPhysicalJets.lean'
old = git('show', BASE + ':' + path)
assert old == verify(owner['base_source']) == (REPO / path).read_bytes()
new = verify(owner['candidate_source'])
assert new.splitlines(keepends=True)[:161] == old.splitlines(keepends=True)[:161]
marker = b'/-- Common low order and loss are chosen before the component.'
assert old[old.index(marker):] == new[new.index(marker):]
assert b'maxHeartbeats' not in new and b'maxRecDepth' not in new
assert not any(x in new for x in [b' sorry', b' axiom ', b'native_decide', b'unsafe'])
assert new.splitlines()[:4] == old.splitlines()[:4]
(REPO / path).write_bytes(new)
git('add', '--', path)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert git('diff', '--cached', '--name-only').decode().splitlines() == [path]
assert git('diff', '--cached', '--numstat').decode().split()[:2] == ['115', '15']
tree = git('write-tree').decode().strip()
rows = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in rows)
deleted = sum(int(x.split()[1]) for x in rows)
assert added == 3022 and deleted == 0 and added <= 20000
assert git('show', tree + ':src/ContinuousFlexibility.lean') == git('show', BASE + ':src/ContinuousFlexibility.lean')
plan = {'label': 149, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
        'main': MAIN, 'last_full_green': GREEN, 'owner': {'path': str(owner_path),
        'sha256': digest(owner_bytes)}, 'source': owner['candidate_source'],
        'target': path, 'preimage': owner['base_source'],
        'independent_review': owner['independent_review'],
        'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
        'delta': {'added': 115, 'deleted': 15}, 'source_total': 4210,
        'source_all_total': 4214, 'root_imports': 4151,
        'created_at': datetime.now(timezone.utc).isoformat(),
        'scope': 'One independently reviewed private proof split; public contracts and successful helper prefix unchanged. Full CI required; 41 reference modules held.'}
payload = [{'path': path, 'mode': '100644', 'type': 'blob', 'content': new.decode()}]
(ROOT / 'n04-ci149-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
pb = json.dumps(payload, ensure_ascii=False).encode()
(ROOT / 'n04-ci149-tree-payload.json').write_bytes(pb)
print(json.dumps({'tree': tree, 'source_lines': owner['candidate_source']['lines'],
    'delta': plan['delta'], 'added_lean_since_full_green': added,
    'payload_codepoints': len(pb.decode()), 'payload_sha256': digest(pb)}))
