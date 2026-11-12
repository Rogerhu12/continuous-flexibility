import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = '34a496f78ec2c9f35f74d2eb3dfd48a1d4190909'
BASE_TREE = '6976c913d75d04075537b04c6c31fd52b82742c2'
MAIN = '43c5eea670bb872c0e0ae7c9cbe88097c6078fef'
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
assert cp['current_ci']['label'] == 154 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
owner_specs = [
    ('root/repair154/CanonicalActualPositiveFiniteFactoryCI154ReviewedManifest.json',
     '4960928b7e81441780715a55bff60020fe02ea940e0cbfa08f693ed6c6ff640a'),
    ('quantitative/repair154/CanonicalPositiveSourceJetBoundsCI154RepairReviewedManifest.json',
     '6555989ce3412a99a89eee4351ff76ef54297ee773bdc1de83bf93d5f6c0bf76')]
groups, sources = [], []
for name, sha in owner_specs:
    owner_path = ROOT / 'n04-drafts' / name
    ob = owner_path.read_bytes()
    assert digest(ob) == sha
    owner = json.loads(ob)
    candidate = json.loads(verify(owner['candidate_manifest']))
    review_info = owner.get('independent_review', owner.get('independent_full_review'))
    review = json.loads(verify(review_info))
    assert candidate['actual_base']['head'] == owner['actual_base']['head'] == BASE
    assert candidate['actual_base']['tree'] == owner['actual_base']['tree'] == BASE_TREE
    ss = candidate.get('sources', [candidate.get('source')])
    osources = owner.get('sources', [owner.get('source')])
    rsources = review.get('sources', [review.get('source')])
    assert len(ss) == len(osources) == len(rsources)
    for csource, osource, rsource in zip(ss, osources, rsources):
        for key in ['path', 'sha256', 'blob', 'lines']:
            assert csource[key] == osource[key] == rsource[key]
    verify(candidate['base'])
    verify(candidate['diff'])
    verify(candidate.get('cached_diagnostic', candidate.get('actual_cached_log')))
    for item in candidate['actual_providers'] + review['actual_providers_verified']:
        verify(item)
    for item in review.get('additional_actual_providers', []):
        verify(item)
    if 'new_shared_provider' in candidate:
        verify(candidate['new_shared_provider'])
        verify(candidate['new_shared_provider_independent_review'])
        verify(candidate['previous_static_full_review'])
    for item in ss:
        new = verify(item)
        path = item['target']
        if (REPO / path).exists():
            old = git('show', BASE + ':' + path)
            assert old == verify(candidate['base']) == (REPO / path).read_bytes()
            for match in re.finditer(rb'(?m)^theorem ([^\s]+)', old):
                begin = match.start()
                header = old[begin:old.index(b' := by', begin)]
                assert header in new, match.group(1)
        else:
            assert path.endswith('/CanonicalPositiveSourceInteriorDivision.lean')
        assert not re.search(rb'\b(?:sorry|axiom|native_decide|unsafe|maxHeartbeats|maxRecDepth)\b', new)
        sources.append(item)
    groups.append({'owner': {'path': str(owner_path), 'sha256': sha},
                   'candidate_manifest': owner['candidate_manifest'],
                   'independent_review': review_info,
                   'sources': ss, 'preimage': candidate['base'], 'diff': candidate['diff']})
assert len(sources) == 3
assert len({x['target'] for x in sources}) == 3
assert sources[0]['blob'] == '1578500670d565ad7ddd08d0345ae0fea8179346'
for item in sources:
    (REPO / item['target']).write_bytes(verify(item))
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
paths = sorted([x['target'] for x in sources] + ['src/ContinuousFlexibility.lean'])
git('add', '--', *paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert git('diff', '--cached', '--name-only').decode().splitlines() == paths
tree = git('write-tree').decode().strip()
rows = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in rows)
deleted = sum(int(x.split()[1]) for x in rows)
assert added <= 20000
source_total = len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean')))
all_total = len(list((REPO / 'src').rglob('*.lean')))
root_imports = sum(line.startswith('import ') for line in (REPO / 'src/ContinuousFlexibility.lean').read_text().splitlines())
assert (source_total, all_total, root_imports) == (4211, 4215, 4152)
plan = {'label': 155, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
        'main_checked': MAIN, 'main_integrated': '89e539ccf7e9c558467cf875f44dcff9490ce271',
        'additional_parents': [], 'last_full_green': GREEN, 'groups': groups,
        'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
        'source_total': source_total, 'source_all_total': all_total, 'root_imports': root_imports,
        'created_at': datetime.now(timezone.utc).isoformat(),
        'scope': 'Two independently reviewed exact CI154 repairs with one shared complete-function transport leaf; genuine per-source proof split, original actual functions and numerical choices, default limits. Main N01c/N05 integration remains pending dependency-complete batches under the hard20000-line limit.'}
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()} for p in paths]
(ROOT / 'n04-ci155-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
pb = json.dumps(payload, ensure_ascii=False).encode()
(ROOT / 'n04-ci155-tree-payload.json').write_bytes(pb)
print(json.dumps({'tree': tree, 'sources': len(sources),
    'added_lean_since_full_green': added, 'source_total': source_total,
    'payload_codepoints': len(pb.decode()), 'payload_sha256': digest(pb)}))
