import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
mf = root / 'n04-drafts/positive/gateway/n01c-n02-compat/ReturnCorrectionBufferedCollarsParameterOrderCandidateManifest.json'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)

def verify(item):
    data = Path(item['path']).read_bytes()
    assert digest(data) == item['sha256'], item['path']
    assert git('hash-object', item['path']).decode().strip() == item['blob']
    assert len(data.splitlines()) == item['lines']
    return data

mb = mf.read_bytes()
assert digest(mb) == '4f69d050d17db24a8b6313d4b6c203a9714263425dd1d5d89830cd8bf17ce8c6'
m = json.loads(mb)
old, new = verify(m['base']), verify(m['source'])
verify(m['exact_diff'])
assert old == git('show', m['base']['ref'] + ':' + m['source']['target'])
for provider in m['providers']:
    verify(provider)
expected = old.decode()
for before, after in m['literal_changes']:
    assert expected.count(before) == 1
    expected = expected.replace(before, after)
assert expected.encode() == new
def heads(data):
    result = []
    for match in re.finditer(rb'(?m)^(?:private )?theorem ([^\s]+)', data):
        result.append(data[match.start():data.index(b' := by', match.start())])
    return result
assert heads(old) == heads(new) and len(heads(new)) == 3
assert len(old.splitlines()) == len(new.splitlines()) == 294
assert b'maxHeartbeats' not in new and b'maxRecDepth' not in new
record = {
    'kind': 'independent_full_source_actual_buffered_collar_parameter_order_review',
    'status': 'PASSED_STATIC_SOURCE_REVIEW_UNCOMPILED', 'reviewer': '/root',
    'candidate_manifest': {'path': str(mf), 'sha256': digest(mb)},
    'source': m['source'], 'base': m['base'], 'exact_diff': m['exact_diff'],
    'verified_providers': m['providers'],
    'read_scope': ['Complete candidate294 and complete three-hunk diff; the exact literal reverse recovers the c5 Git preimage.',
        'Actual ReturnCorrectionSpeedGap94-158 contract and proof; the full common-neighborhood consumer and both public assemblies.',
        'Neighborhood restriction contract and its preceding independently verified same-D parameter-order port.'],
    'checks': [
        'The chosen parameterLoss is supplied by the actual k=1 corrected-speed estimate before choosing any common low order or final state neighborhood.',
        'The new base=max(base,1+loss+parameterLoss) yields both unchanged base monotonicity and the exact new high-order premise. The actual herror call receives that same base and same epsilon.',
        'The positive epsilon remains the minimum of epsilon,1/2,K inverse,and lam/(4UV), retaining the actual same coefficient gap and the same buffered cutoff and radial cell.',
        'On derivative support, the same discriminant lower bound and radial upper bound control half the characteristic gap; both actual reflected error terms use the single herror. Off support the correction vanishes literally.',
        'The two final public certificates preserve the actual half-width cutoff, endpoints, support, component data and original return-corrected flow, retaining N01 for the same D/T/S/C and same spatial loss.',
        'All three complete declaration heads, imports/options and every byte beyond the three specified literal changes are identical to the pinned preimage. Source/base/diff/provider fingerprints verified independently.'],
    'compiled': False,
    'scope_limits': ['No Lean run, CI query or source/index/ref mutation; this is a full static review, not compilation evidence.',
        'The complete selected dependency graph and new-main integration remain separate gates.'],
    'reviewed_at': datetime.now(timezone.utc).isoformat()}
out = root / 'n04-drafts/root/recovery/reviews/ReturnCorrectionBufferedCollarsParameterOrderIndependentReview.json'
out.write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'path': str(out), 'sha256': digest(out.read_bytes()), 'blob': git('hash-object', str(out)).decode().strip(), 'source_lines': 294, 'preserved_heads': 3}))
