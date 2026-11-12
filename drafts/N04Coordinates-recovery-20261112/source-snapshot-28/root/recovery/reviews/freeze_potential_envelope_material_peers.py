import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
MATHLIB = Path('/workspace/scratch/continuous-flexibility-mathlib')
MANIFEST = ROOT / 'n04-drafts/audit/reconstructed/ActualPositiveReferencePotentialCandidateManifest.json'

def ident(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': subprocess.check_output(['git', 'hash-object', str(path)], cwd=REPO).decode().strip(),
            'lines': len(data.splitlines())}

def verify(item):
    actual = ident(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']
    return Path(item['path']).read_text()

mi = ident(MANIFEST)
assert mi['sha256'] == 'd8f564fcc88bfa60fd6683a5e60d0c062a68ec18a615006eb78c4816d9a32bdd'
mf = json.loads(MANIFEST.read_text())
sources = mf['sources'][:2]
assert sum(s['lines'] for s in sources) == 410
for item in sources:
    source = verify(item)
    assert re.findall(r'(?m)^import (.+)$', source) == item['imports']
    assert re.findall(r'(?m)^theorem ([^\s]+)', source) == item['public_names']
    assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', source)
    for name in item['public_names']:
        r = subprocess.run(['rg', '-l', r'\b' + name + r'\b', 'src/ContinuousFlexibility'], cwd=REPO, capture_output=True)
        assert r.returncode == 1 and not r.stdout
for item in mf['actual_provider_refs'] + mf['pinned_api_refs']:
    verify(item)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB).decode().strip() == mf['pinned_mathlib_commit']
additional = [ident(ROOT / 'n04-drafts/positive/reconstructed' / filename) for filename in [
    'PositiveReferenceFinitePrescribed.lean', 'PositiveReferencePrescribedCosts.lean',
    'PositiveReferenceFinitePrescribedReviewedManifest.json', 'PositiveReferencePrescribedCostsReviewedManifest.json']]
for entry in additional[2:]:
    owner = json.loads(Path(entry['path']).read_text())
    verify(owner['source'])
    verify(owner['independent_review'])
additional_apis = [ident(MATHLIB / filename) for filename in [
    'Mathlib/Analysis/Normed/Group/Bounded.lean',
    'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',
    'Mathlib/Analysis/Calculus/IteratedDeriv/FaaDiBruno.lean']]
out = Path(__file__).parent / 'ActualPositiveReferencePotentialEnvelopeMaterialIndependentReview.json'
assert not out.exists()
review = {
    'kind': 'independent_full_source_radial_reference_potential_envelope_and_actual_material_estimate',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED', 'reviewer': '/root',
    'candidate_manifest': mi, 'sources': sources,
    'actual_provider_identities_verified': mf['actual_provider_refs'],
    'additional_actual_providers': additional,
    'pinned_api_identities_verified': mf['pinned_api_refs'] + additional_apis,
    'pinned_mathlib_commit': mf['pinned_mathlib_commit'],
    'read_scope': [
        'Complete159 scalar envelope and251 actual material source, including every finite-prefix sum, power, actual-family projection and point-range argument.',
        'Full79 actual partition provider; original inverse276 theorem interface and preserved family selection, with its full independent review and owner manifest verified.',
        'Full148 actual prescribed-width reference geometry provider, full160 actual endpoint-data supplier, full161 prescribed costs, range-geometry fields and the selected finite radial Taylor definitions.',
        'Pinned iteratedDeriv product/negative/successor APIs, real rpow multiplication, and the actual compact continuous norm-bound provider including its to_additive name.'
    ],
    'checks': [
        'The generic product estimate keeps both zeroth jets. The partition estimate uses positive inverse-coordinate derivatives only; the inverse value itself is used only as the outer evaluation point, including at order zero.',
        'For order N the true flux potential -H(chi)*(w*H_prime composed with chi)_prime uses w through N+1, H through N+2 and chi through N+1. The exact resulting power is 2*N+3, and its coefficient precedes all functions and input envelopes.',
        'The material consumer returns the exact C0/B/finite certificate from the reviewed inverse supplier before any spatial order. It does not re-run a finite factory to select a different B, width, coordinate, inverse or height.',
        'For a fixed s, D=1+sum(A0(k),k<=s+2) uniformly controls all required order constants. The same scaled sample W=C0*E0>=1 permits each exponent increase; no unscaled E0>=1 claim is made.',
        'The physical profile jets are bounded once on the fixed closed annulus, before component and evaluation point. The actual range geometry places chi(x) in the original physical component and hence in that annulus.',
        'Actual prescribed finite radial data reconstruct precisely the displayed delta/Y/H. The selected inverse is Function.invFun of that same Y, and its positive derivatives are exactly the existing supplier outputs.',
        'The final numerical coefficient and exponent are bounded by a single M>=1 without changing the original family. All source/provider/review hashes are exact, both public names have no installed collision, and no limits or frozen target statements change.'
    ],
    'provider_note': 'The actual positiveReferenceFiniteRadialJets_prescribed theorem comes from PositiveReferenceFinitePrescribed148, transitively via PositiveReferencePrescribedCosts161; their source and reviewed identities are recorded in addition to the candidate-listed qualitative finite radial provider167.',
    'scope_limits': [
        'This independent review covers only the first159+251 sources. The third141 whole-atlas flux/mixed adapter has a separate reviewer and is not certified by this receipt.',
        'Actual atom packaging, the negative potential, state-dependent CurrentJets and the complete canonical certificate remain separate obligations.',
        'Static source review only; the full selected source graph has not been elaborated. No active source/index/ref/compiler/CI changes.'
    ],
    'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
