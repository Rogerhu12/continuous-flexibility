import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = 'd3518effba4e07790e04e66cdf347cde1daa6f71'
BASE_TREE = 'f42883129f85f117a2f5ab4ed3e4d5f951fbdcf2'
MAIN = 'e32286d7722222933069431d785efd7904dd8e22'
GREEN = '03e526021c371413f03fc0ce052476b63e105361'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(item):
    data = Path(item['path']).read_bytes()
    assert digest(data) == item['sha256'], item['path']
    assert git('hash-object', item['path']).decode().strip() == item['blob']
    assert len(data.splitlines()) == item['lines']
    return data

assert git('rev-parse', 'HEAD').decode().strip() == BASE
assert git('rev-parse', 'HEAD^{tree}').decode().strip() == BASE_TREE
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
assert git('rev-parse', 'MERGE_HEAD').decode().strip() == MAIN
assert not git('diff', '--name-only')
assert git('diff', '--cached', '--name-only').decode().splitlines() == ['docs/LEAD_HANDOFF.md']
assert (REPO / 'docs/LEAD_HANDOFF.md').read_bytes() == git('show', MAIN + ':docs/LEAD_HANDOFF.md')
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert cp['current_ci']['label'] == 151 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
owner_path = ROOT / 'n04-drafts/quantitative/repair151/CanonicalRootHeightJetsCI151RepairReviewedManifest.json'
ob = owner_path.read_bytes()
assert digest(ob) == 'e3ce7d32eb81e07e718a9520f7e644fff85fa7c4bace4fa05384a81bfba2b230'
owner = json.loads(ob)
candidate = json.loads(verify(owner['candidate_manifest']))
peer = owner['independent_review']
review = json.loads(verify(peer))
assert peer['sha256'] == 'e96acd5c02ddf4ec983a8ad9a8fe5e95d7d87c6a9ff4f704d268ee91c9536920'
assert owner['actual_base'] == candidate['actual_base'] == review['actual_base']
assert owner['actual_base']['head'] == BASE and owner['actual_base']['tree'] == BASE_TREE
assert review['source'] == owner['source'] == candidate['source']
for key in ['base', 'source', 'diff', 'actual_cached_log', 'previous_reviewed_repair']:
    verify(candidate[key])
for item in candidate['providers_checked'] + review['verified_actual_providers']:
    verify(item)
path = candidate['source']['target']
assert path == 'src/ContinuousFlexibility/Analysis/CanonicalRootHeightJets.lean'
old = git('show', BASE + ':' + path)
assert old == verify(candidate['base']) == (REPO / path).read_bytes()
new = verify(candidate['source'])
name = b'theorem n04b_exists_common_root_heightJets'
def public_header(data):
    begin = data.index(name)
    return data[begin:data.index(b' := by', begin)]
assert public_header(old) == public_header(new)
assert old[:old.index(b'/-- The common neighborhood')] == new[:new.index(b'private theorem relativeHeightQuotient_allJets_fixed_loss')]
old_prefix = old[old.index(name):old.index(b'  have hqjets :=')]
new_prefix = new[new.index(name):new.index(b'  have hquotient :')]
assert old_prefix.replace(b'relativeHeightProduct_allJets_fixed_loss', b'relativeHeightQuotient_allJets_fixed_loss') == new_prefix
assert b'maxHeartbeats' not in new and b'maxRecDepth' not in new
assert not any(x in new for x in [b' sorry', b' axiom ', b'native_decide', b'unsafe'])
(REPO / path).write_bytes(new)
git('add', '--', path)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
paths = git('diff', '--cached', '--name-only').decode().splitlines()
assert paths == ['docs/LEAD_HANDOFF.md', path]
delta = git('diff', '--cached', '--numstat', '--', path).decode().split()
tree = git('write-tree').decode().strip()
rows = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in rows)
deleted = sum(int(x.split()[1]) for x in rows)
assert added <= 20000
plan = {'label': 152, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
        'main': MAIN, 'additional_parents': [MAIN], 'last_full_green': GREEN,
        'owner': {'path': str(owner_path), 'sha256': digest(ob)}, 'source': candidate['source'],
        'target': path, 'preimage': candidate['base'], 'independent_review': peer,
        'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
        'delta': {'added': int(delta[0]), 'deleted': int(delta[1])},
        'source_total': 4210, 'source_all_total': 4214, 'root_imports': 4151,
        'created_at': datetime.now(timezone.utc).isoformat(),
        'scope': 'One independently reviewed generic quotient proof split and current-main documentation merge. Same actual geometry, public contracts and resource limits. Full CI required; 41 reference modules held.'}
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()} for p in paths]
(ROOT / 'n04-ci152-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
pb = json.dumps(payload, ensure_ascii=False).encode()
(ROOT / 'n04-ci152-tree-payload.json').write_bytes(pb)
print(json.dumps({'tree': tree, 'source_lines': candidate['source']['lines'],
    'delta': plan['delta'], 'added_lean_since_full_green': added,
    'payload_codepoints': len(pb.decode()), 'payload_sha256': digest(pb)}))
