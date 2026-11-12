"""Record the exact private quotient specialization without changing prior evidence."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/workspace/scratch/bbbea77e4163')
OLD = ROOT / 'n04-reviewed-provider-rebindings-ci151.json'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify(item):
    b = Path(item['path']).read_bytes()
    assert hashlib.sha256(b).hexdigest() == item['sha256']
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == item['blob']

assert digest(OLD) == '36423787e208853308e5f146129d0907541b4f7f9eb4f8fa663b2e8bda7e588e'
graph = json.loads(OLD.read_text())
plan_path = ROOT / 'n04-ci152-plan.json'
plan = json.loads(plan_path.read_text())
assert plan['head_before'] == 'd3518effba4e07790e04e66cdf347cde1daa6f71'
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
        'scope': 'Exact CI151 private generic quotient specialization; same product base/loss/envelope and public declarations.'}
assert not any(x['before'] == edge['before'] and x['after'] == edge['after']
    for x in graph['transitions'].setdefault(module, []))
graph['transitions'].setdefault(module, []).append(edge)
graph['reviews'].append({'path': peer['path'], 'sha256': peer['sha256']})
assert sum(map(len, graph['transitions'].values())) == 27
graph['prior_graph'] = {'path': str(OLD), 'sha256': digest(OLD)}
graph['extension_plan'] = {'path': str(plan_path), 'sha256': digest(plan_path)}
out = ROOT / 'n04-reviewed-provider-rebindings-ci152.json'
assert not out.exists()
out.write_text(json.dumps(graph, ensure_ascii=False, indent=2) + '\n')
old_script = ROOT / 'n04-preflight-reference-family-ci151.py'
script = old_script.read_text().replace("ROOT / 'n04-reviewed-provider-rebindings-ci151.json'",
    "ROOT / 'n04-reviewed-provider-rebindings-ci152.json'").replace(
    '36423787e208853308e5f146129d0907541b4f7f9eb4f8fa663b2e8bda7e588e', digest(out))
new_script = ROOT / 'n04-preflight-reference-family-ci152.py'
assert not new_script.exists()
new_script.write_text(script)
print(json.dumps({'graph': str(out), 'sha256': digest(out),
    'modules': len(graph['transitions']), 'transitions': 27,
    'preflight_script': str(new_script), 'preflight_script_sha256': digest(new_script)}))
