"""Extend the immutable prior graph with the five exact, fully reviewed CI147 repairs."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/workspace/scratch/bbbea77e4163')
OLD = ROOT / 'n04-reviewed-provider-rebindings.json'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify(item):
    raw = Path(item['path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == item['sha256']
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == item['blob']

assert digest(OLD) == '2b17d7305dcc418a0bd9f0bb010e7f479a96bee22fe661ad3a3d1ca5cccf34b1'
graph = json.loads(OLD.read_text())
plan_path = ROOT / 'n04-ci148-plan.json'
plan = json.loads(plan_path.read_text())
assert plan['parent'] == '2058ced3cbf364e7e3ec9980dc76a90785890554'
review_for = {}
for item in plan['reviews']:
    verify(item)
    review = json.loads(Path(item['path']).read_text())
    verify(review['candidate_manifest'])
    if 'rows' in review:
        targets = [x['target'] for x in review['rows']]
    elif 'sources' in review:
        targets = [x['target'] for x in review['sources']]
    else:
        targets = [review['target_path']]
    for target in targets:
        assert target not in review_for
        review_for[target] = item
    graph['reviews'].append({'path': item['path'], 'sha256': item['sha256']})
assert len(review_for) == 5
for item in plan['files']:
    before, after = item['before'], item['after']
    verify(before)
    verify(after)
    target = item['target_path']
    review = review_for[target]
    module = target.removeprefix('src/').removesuffix('.lean').replace('/', '.')
    edge = {'before': before['blob'], 'after': after['blob'],
        'before_source': before, 'after_source': after,
        'review': review['path'], 'review_sha256': review['sha256'],
        'scope': 'Exact CI147 repair; all public contracts unchanged. One existing-provider import or private proof elaboration only.'}
    assert not any(x['before'] == edge['before'] and x['after'] == edge['after']
        for x in graph['transitions'].get(module, []))
    graph['transitions'].setdefault(module, []).append(edge)
assert sum(map(len, graph['transitions'].values())) == 23
graph['prior_graph'] = {'path': str(OLD), 'sha256': digest(OLD)}
graph['extension_plan'] = {'path': str(plan_path), 'sha256': digest(plan_path)}
out = ROOT / 'n04-reviewed-provider-rebindings-ci148.json'
assert not out.exists()
out.write_text(json.dumps(graph, ensure_ascii=False, indent=2) + '\n')
old_script = ROOT / 'n04-preflight-reference-family.py'
script = old_script.read_text().replace("ROOT / 'n04-reviewed-provider-rebindings.json'",
    "ROOT / 'n04-reviewed-provider-rebindings-ci148.json'").replace(
    '2b17d7305dcc418a0bd9f0bb010e7f479a96bee22fe661ad3a3d1ca5cccf34b1', digest(out))
new_script = ROOT / 'n04-preflight-reference-family-ci148.py'
assert not new_script.exists()
new_script.write_text(script)
print(json.dumps({'graph': str(out), 'sha256': digest(out),
    'modules': len(graph['transitions']), 'transitions': 23,
    'preflight_script': str(new_script), 'preflight_script_sha256': digest(new_script)}))
