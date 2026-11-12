import difflib
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = ROOT / 'n04-drafts/positive/compatibility/main-c9-mixed-provider'
MP = BASE / 'LocalMixedCommonProviderCandidateManifest.json'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def ident(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': git('hash-object', str(path)).decode().strip(), 'lines': len(b.splitlines())}

def verify(item):
    actual = ident(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']
    return Path(item['path']).read_text()

mi = ident(MP)
assert mi['sha256'] == '6cda0a1d8f7e77627e69c9db59c57e806ccffc4b066d1cce86d3c1b9baecbc42'
mf = json.loads(MP.read_text())
new, old, diff, provider = map(verify, [mf[k] for k in ['source', 'base', 'diff', 'selected_provider']])
assert old.encode() == git('show', mf['active_base'] + ':' + mf['target_path'])
assert old.encode() == git('show', 'bd249b94d15dd2242e189bcd91c7e378ea7875d9:' + mf['target_path'])
provider_path = 'src/ContinuousFlexibility/Analysis/N01cSpatialParameterComposition.lean'
assert provider.encode() == git('show', mf['main_ref'] + ':' + provider_path)
assert provider.encode() == git('show', 'b629bc27223b74ed17e9fd76fbb8212dcc9163f1:' + provider_path)
start = old.index('\n/-- Subtraction of two fields smooth')
end = old.index('\n/-- A local source factor', start)
assert new == 'import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition\n' + old[:start] + old[end:]
assert diff == ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
    fromfile='active/' + mf['target_path'], tofile='candidate/' + mf['target_path']))
assert re.findall(r'(?m)^theorem ([^\s]+)', new) == [
    'mixedDerivative_eq_of_germ', 'mixedDerivative_mul_of_contDiffOn', 'exists_local_mixedMultiplier_constant']
assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', new)
visiting, visited = set(), {}
def walk(module):
    assert module not in visiting, module
    if module in visited:
        return
    visiting.add(module)
    path = 'src/' + module.replace('.', '/') + '.lean'
    data = git('show', mf['main_ref'] + ':' + path)
    assert module != 'ContinuousFlexibility.Analysis.LocalMixedProductBounds'
    deps = re.findall(r'(?m)^import (ContinuousFlexibility\S+)', data.decode())
    for dep in deps:
        walk(dep)
    visiting.remove(module)
    visited[module] = {'path': path, 'sha256': hashlib.sha256(data).hexdigest(),
                       'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
                       'imports': deps}
walk('ContinuousFlexibility.Analysis.N01cSpatialParameterComposition')
assert len(visited) == mf['provider_closure_count'] == 76
out = Path(__file__).parent / 'LocalMixedCommonProviderIndependentReview.json'
assert not out.exists()
review = {
    'kind': 'independent_full_source_local_mixed_common_provider_supersession',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED', 'reviewer': '/root',
    'candidate_manifest': mi, 'source': mf['source'], 'base': mf['base'], 'diff': mf['diff'],
    'selected_provider': mf['selected_provider'], 'provider_ref': mf['main_ref'],
    'read_scope': ['Full105 candidate and complete35-line diff, including the removed actual mixed-subtraction proof.',
                   'Actual current-main mixed-subtraction theorem and complete proof plus its direct imports; every active call and its named arguments.',
                   'All76 upstream project import entries mechanically resolved from exact c9 Git objects with cycle and consumer-backedge checks.'],
    'checks': [
        'The candidate is exactly the active125 source with one direct import added and only its duplicate subtraction declaration/documentation/proof removed. All three remaining complete declarations and proofs are byte-identical.',
        'The selected main proposition is the same subtraction identity for actual mixed derivatives on the same open set. Its actual Fréchet-word proof supplies the same mathematical interface.',
        'Explicit open-set/smoothness/orders/point-membership arguments are unchanged. The implicit domain name U becomes Omega and f/g move before the open premise; actual consumers use positional domain inference and compatible named f/g/p.',
        'Both actual34a496 and currentbd249 preimages match, as do c9 and currentb629 provider bytes. The upstream76-module provider closure has no missing project import, cycle or LocalMixedProductBounds backedge.',
        'No new theorem, estimate premise, witness, resource limit or remaining proof-body change is introduced.'
    ],
    'provider_closure': {'modules': len(visited), 'missing_imports': [], 'cycles': [], 'consumer_backedge': False},
    'scope_limits': ['Select this source only in the batch that installs N01cSpatialParameterComposition and its prerequisites; it is outside the minimal first contract cohort.',
                     'This is source/interface review, not elaboration of the combined final tree. No active source/index/ref/compiler/CI changes.'],
    'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
