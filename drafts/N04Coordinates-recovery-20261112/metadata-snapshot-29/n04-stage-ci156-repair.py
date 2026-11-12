import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = 'bd249b94d15dd2242e189bcd91c7e378ea7875d9'
BASE_TREE = '93221bdfea014a7ed555112fe6f2cf136d94df35'
MAIN = '2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d'
GREEN = '03e526021c371413f03fc0ce052476b63e105361'
TARGET = 'src/ContinuousFlexibility/Analysis/CanonicalPositiveSourceJetBounds.lean'
WORKFLOW = '.github/workflows/build.yml'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': git('hash-object', str(path)).decode().strip(), 'lines': len(data.splitlines())}

def verify(item):
    actual = identity(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']
    return Path(item['path']).read_bytes()

assert git('rev-parse', 'HEAD').decode().strip() == BASE
assert git('rev-parse', 'HEAD^{tree}').decode().strip() == BASE_TREE
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
assert not git('status', '--porcelain')
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert cp['current_ci']['label'] == 155 and cp['current_ci']['status'] == 'failure'
assert cp['last_full_green']['sha'] == GREEN
op = ROOT / 'n04-drafts/quantitative/repair155/CanonicalPositiveSourceJetBoundsCI155RepairReviewedManifest.json'
oi = identity(op)
assert oi['sha256'] == 'e0dd141fff5b9f194a322d6f7e36a1cc1b7bcc52edcad0339425b354d15d0bdf'
owner = json.loads(op.read_text())
candidate = json.loads(verify(owner['candidate_manifest']))
review = json.loads(verify(owner['independent_full_review']))
assert candidate['actual_base'] == owner['actual_base'] == review['actual_base'] == {
    'head': BASE, 'tree': BASE_TREE, 'target': TARGET}
assert candidate['source'] == owner['source'] == review['source']
assert owner['independent_full_review']['sha256'] == '84630bed19daf55c1bb38b2c5eda944796e1fbd9396effb1e4c6822f0e356822'
new = verify(candidate['source'])
old = verify(candidate['base'])
assert old == git('show', BASE + ':' + TARGET) == (REPO / TARGET).read_bytes()
assert new.splitlines(True)[:69] == old.splitlines(True)[:69]
tail = b'theorem n04Coordinates_actual_positiveSource_allJets'
assert new[new.index(tail):] == old[old.index(tail):]
for match in re.finditer(rb'(?m)^theorem ([^\s]+)', old):
    begin = match.start()
    header = old[begin:old.index(b' := by', begin)]
    assert header in new
assert re.findall(rb'(?m)^import .+$', old) == re.findall(rb'(?m)^import .+$', new)
assert re.findall(rb'(?m)^set_option .+$', old) == re.findall(rb'(?m)^set_option .+$', new)
assert not re.search(rb'\b(?:sorry|axiom|native_decide|unsafe|maxHeartbeats|maxRecDepth)\b', new)
for item in [candidate['diff'], candidate['cached_log'], candidate['previous_exact_source_review']] + candidate['actual_providers'] + review['actual_providers_verified'] + review['additional_actual_providers']:
    verify(item)
assert git('diff', '--name-only', 'b629bc27223b74ed17e9fd76fbb8212dcc9163f1', MAIN).decode().splitlines() == [WORKFLOW]
workflow = git('show', MAIN + ':' + WORKFLOW)
(REPO / TARGET).write_bytes(new)
(REPO / WORKFLOW).write_bytes(workflow)
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
paths = [WORKFLOW, TARGET]
git('add', '--', *paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert not git('diff')
assert git('diff', '--cached', '--name-only').decode().splitlines() == paths
tree = git('write-tree').decode().strip()
numstat = git('diff', '--numstat', GREEN, tree, '--', '*.lean').decode().splitlines()
added = sum(int(x.split()[0]) for x in numstat)
deleted = sum(int(x.split()[1]) for x in numstat)
assert added <= 20000
source_total = len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean')))
all_total = len(list((REPO / 'src').rglob('*.lean')))
imports = sum(line.startswith('import ') for line in (REPO / 'src/ContinuousFlexibility.lean').read_text().splitlines())
assert (source_total, all_total, imports) == (4211, 4215, 4152)
plan = {'label': 156, 'head_before': BASE, 'base_tree': BASE_TREE, 'tree': tree,
    'main_checked': MAIN, 'main_integrated': '89e539ccf7e9c558467cf875f44dcff9490ce271',
    'additional_parents': [], 'last_full_green': GREEN,
    'owner_manifest': oi, 'candidate_manifest': owner['candidate_manifest'],
    'independent_review': owner['independent_full_review'], 'source': candidate['source'],
    'target': TARGET, 'preimage': candidate['base'], 'diff': candidate['diff'],
    'main_workflow_file_integrated': {'main': MAIN, 'path': WORKFLOW,
        'sha256': hashlib.sha256(workflow).hexdigest(), 'blob': git('hash-object', WORKFLOW).decode().strip(),
        'method': 'Exact workflow-only file copy; main ancestry remains pending dependency-complete source batches.'},
    'added_lean_since_full_green': added, 'deleted_lean_since_full_green': deleted,
    'source_total': source_total, 'source_all_total': all_total, 'root_imports': imports,
    'scope': 'Independently reviewed three-layer proof abstraction for the remaining actual positive source jet file. Same complete public contracts, real functions, witnesses, max/min and numerical envelopes; default limits. Includes exact current-main line-origin artifact reuse workflow. Source/main integration and held reference activation remain gated on full CI.',
    'created_at': datetime.now(timezone.utc).isoformat()}
(ROOT / 'n04-ci156-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()} for p in paths]
text = json.dumps(payload, ensure_ascii=False)
(ROOT / 'n04-ci156-tree-payload.json').write_text(text)
print(json.dumps({'tree': tree, 'added_lean_since_full_green': added, 'paths': paths,
                  'payload_codepoints': len(text), 'payload_sha256': hashlib.sha256(text.encode()).hexdigest()}))
