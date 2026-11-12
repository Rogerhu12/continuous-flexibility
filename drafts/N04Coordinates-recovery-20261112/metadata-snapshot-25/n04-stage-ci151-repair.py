import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = 'f68cf109aeb61c24491d549db5730b1bdba7dc14'
BASE_TREE = '38248438ccc4218057e13fcab09874f491a2839e'
MAIN = 'ecd4e991a1d86d00324403bacfeecb760d7fbcdd'
GREEN = '03e526021c371413f03fc0ce052476b63e105361'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(item):
    b = Path(item['path']).read_bytes()
    assert digest(b) == item['sha256'], item['path']
    assert git('hash-object', item['path']).decode().strip() == item['blob']
    assert len(b.splitlines()) == item['lines']
    return b

assert git('rev-parse', 'HEAD').decode().strip() == BASE
assert git('rev-parse', 'HEAD^{tree}').decode().strip() == BASE_TREE
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
subprocess.run(['git', 'merge-base', '--is-ancestor', MAIN, BASE], cwd=REPO, check=True)
assert not git('status', '--porcelain')
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert cp['current_ci']['label'] == 150 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
owner_path = ROOT / 'n04-drafts/quantitative/repair150/CanonicalRootHeightJetsCI150RepairReviewedManifest.json'
ob = owner_path.read_bytes()
assert digest(ob) == 'bb2e35248bdc0330a466fbdb706eb4236c74b958df7edf97c4a4855ac569416f'
owner = json.loads(ob)
candidate = json.loads(verify(owner['candidate_manifest']))
assert len(owner['independent_reviews']) == 1
peer = owner['independent_reviews'][0]
review = json.loads(verify(peer))
assert peer['sha256'] == 'cebe90683bbae13aac92de8136ab07ada3beef6e32f17cb994a070a52f72a93e'
assert owner['actual_head'] == BASE and owner['actual_tree'] == BASE_TREE
assert review['source'] == owner['source'] == candidate['after']
for key in ['base', 'after', 'diff', 'cached_ci_log']:
    verify(candidate[key])
for x in candidate['providers'] + review['verified_providers']:
    verify(x)
path = candidate['target']
assert path == 'src/ContinuousFlexibility/Analysis/CanonicalRootHeightJets.lean'
old = git('show', BASE + ':' + path)
assert old == verify(candidate['base']) == (REPO / path).read_bytes()
new = verify(candidate['after'])
assert old.splitlines(keepends=True)[:157] == new.splitlines(keepends=True)[:157]
assert old[:old.index(b' := by', old.index(b'theorem n04b_exists_common_root_heightJets'))] == new[:new.index(b' := by', new.index(b'theorem n04b_exists_common_root_heightJets'))]
assert b'maxHeartbeats' not in new and b'maxRecDepth' not in new
assert not any(x in new for x in [b' sorry', b' axiom ', b'native_decide', b'unsafe'])
(REPO / path).write_bytes(new)
git('add', '--', path)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert git('diff', '--cached', '--name-only').decode().splitlines() == [path]
delta = git('diff', '--cached', '--numstat', '--', path).decode().split()
tree = git('write-tree').decode().strip()
rows = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in rows)
deleted = sum(int(x.split()[1]) for x in rows)
assert added <= 20000
plan = {'label': 151, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
        'main': MAIN, 'last_full_green': GREEN,
        'owner': {'path': str(owner_path), 'sha256': digest(ob)}, 'source': candidate['after'],
        'target': path, 'preimage': candidate['base'], 'independent_review': peer,
        'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
        'delta': {'added': int(delta[0]), 'deleted': int(delta[1])},
        'source_total': 4210, 'source_all_total': 4214, 'root_imports': 4151,
        'created_at': datetime.now(timezone.utc).isoformat(),
        'scope': 'One independently reviewed exact quotient/inverse function transport repair; first157 lines and public contracts unchanged. Full CI required; 41 reference modules held.'}
payload = [{'path': path, 'mode': '100644', 'type': 'blob', 'content': new.decode()}]
(ROOT / 'n04-ci151-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
pb = json.dumps(payload, ensure_ascii=False).encode()
(ROOT / 'n04-ci151-tree-payload.json').write_bytes(pb)
print(json.dumps({'tree': tree, 'source_lines': candidate['after']['lines'],
    'delta': plan['delta'], 'added_lean_since_full_green': added,
    'payload_codepoints': len(pb.decode()), 'payload_sha256': digest(pb)}))
