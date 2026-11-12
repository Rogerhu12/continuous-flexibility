"""Record the exact point transport repair without changing prior evidence."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/workspace/scratch/bbbea77e4163')
OLD = ROOT / 'n04-reviewed-provider-rebindings-ci149.json'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify(item):
    b = Path(item['path']).read_bytes()
    assert hashlib.sha256(b).hexdigest() == item['sha256']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == item['blob']

assert digest(OLD) == '205bed4fecf57bbeab3c8c97586c94e772122b70d0a1df230f490198d177e63b'
graph = json.loads(OLD.read_text())
plan_path = ROOT / 'n04-ci150-plan.json'
plan = json.loads(plan_path.read_text())
assert plan['head_before'] == 'c8299751750decf27765045c36c280d249622f7e'
before, after, peer = plan['preimage'], plan['source'], plan['independent_review']
for item in [before, after, peer]:
    verify(item)
review = json.loads(Path(peer['path']).read_text())
verify(review['candidate_manifest'])
target = plan['target']
module = target.removeprefix('src/').removesuffix('.lean').replace('/', '.')
edge = {'before': before['blob'], 'after': after['blob'],
        'before_source': before, 'after_source': after,
        'review': peer['path'], 'review_sha256': peer['sha256'],
        'scope': 'Exact CI149 typed physical-point transport; public declarations and all other proof bytes unchanged.'}
assert not any(x['before'] == edge['before'] and x['after'] == edge['after']
    for x in graph['transitions'].setdefault(module, []))
graph['transitions'].setdefault(module, []).append(edge)
graph['reviews'].append({'path': peer['path'], 'sha256': peer['sha256']})
assert sum(map(len, graph['transitions'].values())) == 25
graph['prior_graph'] = {'path': str(OLD), 'sha256': digest(OLD)}
graph['extension_plan'] = {'path': str(plan_path), 'sha256': digest(plan_path)}
out = ROOT / 'n04-reviewed-provider-rebindings-ci150.json'
assert not out.exists()
out.write_text(json.dumps(graph, ensure_ascii=False, indent=2) + '\n')
old_script = ROOT / 'n04-preflight-reference-family-ci149.py'
script = old_script.read_text().replace("ROOT / 'n04-reviewed-provider-rebindings-ci149.json'",
    "ROOT / 'n04-reviewed-provider-rebindings-ci150.json'").replace(
    '205bed4fecf57bbeab3c8c97586c94e772122b70d0a1df230f490198d177e63b', digest(out))
new_script = ROOT / 'n04-preflight-reference-family-ci150.py'
assert not new_script.exists()
new_script.write_text(script)
print(json.dumps({'graph': str(out), 'sha256': digest(out),
    'modules': len(graph['transitions']), 'transitions': 25,
    'preflight_script': str(new_script), 'preflight_script_sha256': digest(new_script)}))
