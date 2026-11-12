import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = '11eeb8aebced4bef16f743c11484df9b0c0907a1'
BASE_TREE = '13c563567ec6c0ecdce19ef2f192970d2400b8b2'
MAIN = 'c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
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
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert cp['current_ci']['label'] == 153 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
owner_path = ROOT / 'n04-drafts/quantitative/repair153/CanonicalRootFiniteEndpointBoundsCI153RepairReviewedManifest.json'
ob = owner_path.read_bytes()
assert digest(ob) == '693f3c813312bd57a6dbe0a42f8164f30c775590f192c1fe941f693e412003e1'
owner = json.loads(ob)
candidate = json.loads(verify(owner['candidate_manifest']))
peer = owner['independent_review']
review = json.loads(verify(peer))
assert peer['sha256'] == '0653af8daf3038f61470cd8da4eae38844208c92e7993860f73b4910bcc08f2d'
assert owner['actual_base'] == candidate['actual_base'] == review['actual_base']
assert owner['actual_base']['head'] == BASE and owner['actual_base']['tree'] == BASE_TREE
assert review['source'] == owner['source'] == candidate['source']
for key in ['base', 'source', 'diff', 'actual_cached_log', 'previous_full_source_review']:
    verify(candidate[key])
for item in candidate['actual_direct_and_relative_providers'] + review['actual_providers']:
    verify(item)
path = candidate['source']['target']
assert path == 'src/ContinuousFlexibility/Analysis/CanonicalRootFiniteEndpointBounds.lean'
old = git('show', BASE + ':' + path)
assert old == verify(candidate['base']) == (REPO / path).read_bytes()
new = verify(candidate['source'])
before = b'(add_le_add_left hg 1)'
after = b'(add_le_add le_rfl hg)'
assert old.count(before) == 1 and new.count(after) == 1
assert old.replace(before, after) == new
assert b'maxHeartbeats' not in new and b'maxRecDepth' not in new
assert not any(x in new for x in [b' sorry', b' axiom ', b'native_decide', b'unsafe'])
(REPO / path).write_bytes(new)
git('add', '--', path)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
paths = git('diff', '--cached', '--name-only').decode().splitlines()
assert paths == [path]
delta = git('diff', '--cached', '--numstat', '--', path).decode().split()
assert tuple(map(int, delta[:2])) == (1, 1)
tree = git('write-tree').decode().strip()
rows = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in rows)
deleted = sum(int(x.split()[1]) for x in rows)
assert added <= 20000
plan = {'label': 154, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
        'main_checked': MAIN, 'main_integrated': '89e539ccf7e9c558467cf875f44dcff9490ce271',
        'additional_parents': [], 'last_full_green': GREEN,
        'owner': {'path': str(owner_path), 'sha256': digest(ob)}, 'source': candidate['source'],
        'target': path, 'preimage': candidate['base'], 'independent_review': peer,
        'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
        'delta': {'added': int(delta[0]), 'deleted': int(delta[1])},
        'source_total': 4210, 'source_all_total': 4214, 'root_imports': 4151,
        'created_at': datetime.now(timezone.utc).isoformat(),
        'pending_main': {'sha': MAIN, 'upstream_added_lean': 67562, 'upstream_deleted_lean': 640,
            'reason': 'New main adds N01c and N05 integration exceeding the hard20000-line distance. Repair the existing failed module first, then integrate dependency-complete upstream batches with CI gates; no new held reference sources activated.'},
        'scope': 'Exactly one independently reviewed scalar addition-side repair. Height268 remains byte-identical after CI153 acceptance. Full CI required before further activation.'}
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()} for p in paths]
(ROOT / 'n04-ci154-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
pb = json.dumps(payload, ensure_ascii=False).encode()
(ROOT / 'n04-ci154-tree-payload.json').write_bytes(pb)
print(json.dumps({'tree': tree, 'source_lines': candidate['source']['lines'],
    'delta': plan['delta'], 'added_lean_since_full_green': added,
    'payload_codepoints': len(pb.decode()), 'payload_sha256': digest(pb)}))
