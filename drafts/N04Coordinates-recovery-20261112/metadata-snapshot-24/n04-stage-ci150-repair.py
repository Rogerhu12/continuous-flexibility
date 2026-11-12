import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = 'c8299751750decf27765045c36c280d249622f7e'
BASE_TREE = '595109a492679b00341215a00cbdd10815b2ae39'
MAIN = 'ecd4e991a1d86d00324403bacfeecb760d7fbcdd'
OLD_MAIN = 'c070da70d8df06e5345ff10f63aeff17207f257e'
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
assert not git('status', '--porcelain')
assert git('diff', '--name-only', OLD_MAIN, MAIN).decode().splitlines() == ['.github/workflows/probe.yml']
assert not git('diff', OLD_MAIN, MAIN, '--', 'AGENTS.md', 'docs/tasks/README.md')
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert cp['current_ci']['label'] == 149 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
owner_path = ROOT / 'n04-drafts/quantitative/repair149/CanonicalRootHeightJetsCI149RepairReviewedManifest.json'
ob = owner_path.read_bytes()
assert digest(ob) == '2720040b0f56a0b5e20d409b707f90ea20ed8b88cd5bd3518fbe77ca987a2cd8'
owner = json.loads(ob)
candidate = json.loads(verify(owner['candidate_manifest']))
verify(owner['independent_review'])
assert owner['actual_head'] == BASE and owner['actual_tree'] == BASE_TREE
for key in ['base', 'after', 'diff', 'cached_ci_log']:
    verify(candidate[key])
for x in candidate['providers']:
    verify(x)
path = candidate['target']
assert path == 'src/ContinuousFlexibility/Analysis/CanonicalRootHeightJets.lean'
old = git('show', BASE + ':' + path)
assert old == verify(candidate['base']) == (REPO / path).read_bytes()
new = verify(candidate['after'])
assert old[:old.index(b' := by', old.index(b'theorem n04b_exists_common_root_heightJets'))] == new[:new.index(b' := by', new.index(b'theorem n04b_exists_common_root_heightJets'))]
assert old[:old.index(b'    rw [hy]')] == new[:new.index(b'    have hrootCurrent')]
assert old[old.index(b'  have hreference :'):] == new[new.index(b'  have hreference :'):]
assert b'maxHeartbeats' not in new and b'maxRecDepth' not in new
assert not any(x in new for x in [b' sorry', b' axiom ', b'native_decide', b'unsafe'])
subprocess.run(['git', 'merge', '--no-commit', '--no-ff', 'origin/main'], cwd=REPO, check=True)
assert git('rev-parse', 'MERGE_HEAD').decode().strip() == MAIN
assert git('diff', '--cached', '--name-only').decode().splitlines() == ['.github/workflows/probe.yml']
assert (REPO / '.github/workflows/probe.yml').read_bytes() == git('show', MAIN + ':.github/workflows/probe.yml')
(REPO / path).write_bytes(new)
git('add', '--', path)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == {path, '.github/workflows/probe.yml'}
assert git('diff', '--cached', '--numstat', '--', path).decode().split()[:2] == ['9', '2']
tree = git('write-tree').decode().strip()
rows = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in rows)
deleted = sum(int(x.split()[1]) for x in rows)
assert added == 3029 and deleted == 0 and added <= 20000
assert git('show', tree + ':src/ContinuousFlexibility.lean') == git('show', BASE + ':src/ContinuousFlexibility.lean')
plan = {'label': 150, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
        'main': MAIN, 'additional_parent': MAIN, 'previous_main': OLD_MAIN, 'last_full_green': GREEN,
        'owner': {'path': str(owner_path), 'sha256': digest(ob)}, 'source': candidate['after'],
        'target': path, 'preimage': candidate['base'], 'independent_review': owner['independent_review'],
        'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
        'delta': {'added': 9, 'deleted': 2}, 'source_total': 4210, 'source_all_total': 4214,
        'root_imports': 4151, 'created_at': datetime.now(timezone.utc).isoformat(),
        'main_merge_scope': 'Only upstream probe workflow improves diagnostic capture; no build limits, main build workflow, rules or Lean interfaces changed.',
        'scope': 'One independently reviewed exact point-transport repair; public contracts unchanged. Full CI required; 41 reference modules held.'}
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()}
           for p in ['.github/workflows/probe.yml', path]]
(ROOT / 'n04-ci150-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
pb = json.dumps(payload, ensure_ascii=False).encode()
(ROOT / 'n04-ci150-tree-payload.json').write_bytes(pb)
print(json.dumps({'tree': tree, 'source_lines': candidate['after']['lines'],
    'delta': plan['delta'], 'added_lean_since_full_green': added,
    'payload_codepoints': len(pb.decode()), 'payload_sha256': digest(pb)}))
