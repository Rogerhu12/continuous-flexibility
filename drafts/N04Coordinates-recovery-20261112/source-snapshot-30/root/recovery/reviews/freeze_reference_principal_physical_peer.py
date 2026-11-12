import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
candidate = root / 'n04-drafts/quantitative/primitive-route/reconstructed/ReferencePrincipalPhysicalMaterialJetsCandidateManifest.json'

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.splitlines())}

assert identity(candidate)['sha256'] == 'b746db1fab6d825ba69a19defae473d57e6b8be264d0b97b5e9050f70d715de9'
mf = json.loads(candidate.read_text())
for item in [mf['source'], mf['selected_inverse_profile_owner']] + mf['actual_providers']:
    actual = identity(item['path'])
    assert all(item[k] == actual[k] for k in ('sha256', 'blob', 'lines')), item['path']
source = Path(mf['source']['path']).read_text()
assert not re.search(r'\b(sorry|axiom|unsafe|native_decide)\b|set_option', source)
pattern = r'^(theorem|lemma|def|abbrev)\s+(' + '|'.join(map(re.escape, mf['public_names'])) + r')\b'
scan = subprocess.run(['rg', '-n', pattern, str(root / 'continuous-flexibility/src')], capture_output=True, text=True)
assert scan.returncode == 1 and not scan.stdout
review = {
    'kind': 'independent_full_source_same_positive_sample_physical_principal_factors',
    'candidate_manifest': identity(candidate),
    'source': mf['source'],
    'actual_providers_verified': mf['actual_providers'],
    'selected_inverse_profile_owner': mf['selected_inverse_profile_owner'],
    'additional_pinned_provider': identity('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean'),
    'read_scope': [
        'Full108 source and complete candidate; the previously fully reviewed103 reciprocal-profile producer and its original sample transport.',
        'Actual reference_contDiffOn_iteratedDeriv, n04PositiveComponent_bounds, contDiff_infty_iff_deriv and the to_additive-generated IsCompact.exists_bound_of_continuousOn contract.'
    ],
    'checks': [
        'Only w and wprime/r are bounded by compactness on the fixed closed annulus. Both are smooth on Ioi0 since the actual ambient radius a is positive; no compact bound for inverse w is taken at the vanishing ambient endpoints.',
        'The finite Bool x Fin(N+1) family supplies all derivatives through N. Summing absolute values of its compact bounds gives a single nonnegative prefix constant, with no component or point dependence.',
        'The true reciprocal profile is supplied exclusively by the reviewed103 accumulating-profile and retained-positive-sample theorem, at the unchanged original midpoint host.',
        'The supplied C0 remains fixed. Positivity of E0 and C0>=1 give E0<=C0*E0, while only the supplied proved floor for C0*E0 is used to enlarge real exponents.',
        'M=1+P0+K+A dominates both coefficients and the reciprocal exponent. It is selected before all components, host indices, closed-interval points and derivative orders through N.',
        'The true positive-component endpoint bounds place each physical point in the fixed closed annulus. Both endpoint values are retained, with no false whole-component cell assumption.',
        'Every source/provider identity is exact, the new public name has no active collision, and there are no new axioms, placeholders, unsafe primitives or resource options.'
    ],
    'scope_limits': [
        'The retained reference/control evidence and existing scaled-envelope floor remain explicit; no assertion is made for an unrelated Through03 witness.',
        'This is the physical-factor input for the actual positive principal atoms. It does not itself establish their transformed jets or CurrentJets.',
        'Static source/API review only. No compiler, CI or active source/index/ref action; selected full import closure remains an integration gate.'
    ],
    'reviewer': '/root',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED',
    'compiled': False,
    'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = root / 'n04-drafts/root/recovery/reviews/ReferencePrincipalPhysicalMaterialJetsIndependentReview.json'
assert not out.exists()
out.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(identity(out)))
