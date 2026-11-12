"""Record the exact private specialization repair without changing prior evidence."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/workspace/scratch/bbbea77e4163')
OLD = ROOT / 'n04-reviewed-provider-rebindings-ci148.json'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify(item):
    b = Path(item['path']).read_bytes()
    assert hashlib.sha256(b).hexdigest() == item['sha256']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == item['blob']

assert digest(OLD) == '0ddeba8feb48ce3bd897d07c3bf77e28c85033c5f203f614f24c924e840388d2'
graph = json.loads(OLD.read_text())
plan_path = ROOT / 'n04-ci149-plan.json'
plan = json.loads(plan_path.read_text())
assert plan['head_before'] == 'dc2dd491aa653712df6f739448eed9bb1505166e'
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
        'scope': 'Exact CI148 private proof specialization split; all public declarations and accepted helper prefix unchanged.'}
assert not any(x['before'] == edge['before'] and x['after'] == edge['after']
    for x in graph['transitions'][module])
graph['transitions'][module].append(edge)
graph['reviews'].append({'path': peer['path'], 'sha256': peer['sha256']})
assert sum(map(len, graph['transitions'].values())) == 24
graph['prior_graph'] = {'path': str(OLD), 'sha256': digest(OLD)}
graph['extension_plan'] = {'path': str(plan_path), 'sha256': digest(plan_path)}
out = ROOT / 'n04-reviewed-provider-rebindings-ci149.json'
assert not out.exists()
out.write_text(json.dumps(graph, ensure_ascii=False, indent=2) + '\n')
old_script = ROOT / 'n04-preflight-reference-family-ci148.py'
script = old_script.read_text().replace("ROOT / 'n04-reviewed-provider-rebindings-ci148.json'",
    "ROOT / 'n04-reviewed-provider-rebindings-ci149.json'").replace(
    '0ddeba8feb48ce3bd897d07c3bf77e28c85033c5f203f614f24c924e840388d2', digest(out))
new_script = ROOT / 'n04-preflight-reference-family-ci149.py'
assert not new_script.exists()
new_script.write_text(script)
print(json.dumps({'graph': str(out), 'sha256': digest(out),
    'modules': len(graph['transitions']), 'transitions': 24,
    'preflight_script': str(new_script), 'preflight_script_sha256': digest(new_script)}))
