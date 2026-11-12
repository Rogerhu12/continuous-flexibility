import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
drafts = root / 'n04-drafts'
out = drafts / 'root/recovery/reviews'

def ident(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path': str(p), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest(),
            'lines': len(b.decode().splitlines())}

def verify(r):
    actual = ident(r['path'])
    for k in ('sha256', 'blob', 'lines'):
        if k in r:
            assert actual[k] == r[k], (r['path'], k)
    if 'git_blob' in r:
        assert actual['blob'] == r['git_blob']
    return actual

mf = drafts / 'audit/reconstructed/ActualNegativeReferencePotentialFormulaCandidateManifest.json'
cand = json.loads(mf.read_text())
source = verify(cand['source'])
assert source['sha256'] == '9901ab0f2a3ff035d99d3f420c0b1215a279b53ba99785b06b3e1a9047a7ea7b'
providers = [verify(r) for r in cand['provider_refs']]
extra = [ident(root / 'continuous-flexibility/src/ContinuousFlexibility/Analysis' / f) for f in
         ('N04bActualAtlasGeometry.lean', 'N04bCurrentPartition.lean', 'N04bCanonicalOperator.lean')]
reviews = [ident(drafts / 'audit/reconstructed' / f) for f in
           ('WholeReferenceGaugeReferencePrincipalReviewedManifest.json',
            'ActualReferenceNegativeEndpointDataReviewedManifest.json',
            'WholePositiveReferencePrincipalReviewedManifest.json')]
text = Path(source['path']).read_text()
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', text)
review = {
    'kind': 'independent_full_source_actual_negative_potential_density_cancellation',
    'candidate_manifest': ident(mf), 'source': source,
    'actual_providers_verified': providers, 'additional_actual_providers': extra,
    'selected_provider_reviews': reviews,
    'pinned_mathlib_provider': ident('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Algebra/Group/DivInvMonoid.lean'),
    'read_scope': [
        'Full137 candidate and complete candidate manifest.',
        'Full143 strip potential germs, full100 radial principal formulas, full156 actual negative radial fields, full111 actual negative principal density.',
        'Actual PartA geometry theorem, actual negative physical-domain inclusion, stored typed-atlas/operator fields, and pinned inv_eq_of_mul_eq_one_left.'
    ],
    'checks': [
        'The scalar unit equation forces abs(j) nonzero; multiplying by abs(j) gives h^2*w*abs(j)=1. The pinned inverse API yields abs(j)^(-1)=h^2*w without choosing an orientation or assuming a new slope lower bound.',
        'The generic strip theorem uses actual chart and height germs at G(p). Unit and zero mixed density force the physical mixed coefficient to vanish on the same open strip; its derivatives are justified by that neighborhood equality.',
        'The actual radial density formula and coefficient a=w produce the exact scalar unit equation. Substitution into H*(w*Hprime)prime/abs(Yprime) gives w*H^3*(w*Hprime)prime with the correct powers and sign.',
        'The typed-atlas adapter constructs its actual PartA certificate internally. Inverse MapsTo followed by the actual negative half-domain inclusion puts the same inverse point inside the whole physical component.',
        'Actual reference-state membership and sector follow from the retained hN. The reference coefficient identity and actual whole-component negative density supply all generic premises for the original chart and height.',
        'The stored operator type sign is positive on a negative piece, verified from n04bCanonicalOperatorData and the actual typed index. No positive-piece minus sign is reused.',
        'All candidate/provider identities are exact. This review explicitly adds the actual PartA, physical-domain and operator-definition providers omitted from the short candidate provider list.',
        'No project axiom, sorry, unsafe proof primitive, target weakening or resource increase is introduced.'
    ],
    'scope_limits': [
        'Exact stored potential identity only; it does not assert a whole-half material height tower, uniform potential bound or CurrentJets.',
        'No regularity outside the actual physical open component or replacement of the selected inverse is assumed.',
        'No compiler/CI/active-source/index/ref mutation. Import closure still requires the selected full integration preflight.'
    ],
    'reviewer': '/root', 'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED',
    'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
}
p = out / 'ActualNegativeReferencePotentialFormulaIndependentReview.json'
assert not p.exists()
p.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(p)))

folder = drafts / 'root/reconstructed'
mf = folder / 'CanonicalActualPrescribedReferenceGeometryCandidateManifest.json'
cand = json.loads(mf.read_text())
peerpath = drafts / 'quantitative/recovery/reviews/CanonicalActualPrescribedReferenceGeometryIndependentReview.json'
peer = json.loads(peerpath.read_text())
assert ident(peerpath)['sha256'] == '8c84bd988c499bd3f2b71661e336ca6038a59af6fd85275674e0e254459c1537'
assert peer['source'] == cand['source'] and peer['candidate_manifest'] == ident(mf)
verify(cand['source'])
verify(cand['original_reviewed_source'])
verify(cand['original_reviewed_manifest'])
for r in peer['actual_provider_identities']:
    verify(r)
owner = {
    'kind': 'actual_geometry_on_same_prescribed_reference_family_reviewed_manifest',
    'owner': '/root', 'status': 'STATIC_REVIEWED_HELD_UNCOMPILED',
    'source': cand['source'], 'candidate_manifest': ident(mf),
    'independent_full_review': ident(peerpath),
    'original_source_preserved': cand['original_reviewed_source'],
    'scope': 'The supplied actual order4 reference family is retained in the same V throughout all original geometry/cut/source/radial/transmission/global-transport conclusions. The relative controls and common state neighborhood alone are selected.',
    'compiled': False, 'green_receipt_applies': False,
    'created_at': datetime.now(timezone.utc).isoformat()
}
p = folder / 'CanonicalActualPrescribedReferenceGeometryReviewedManifest.json'
assert not p.exists()
p.write_text(json.dumps(owner, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(p)))
