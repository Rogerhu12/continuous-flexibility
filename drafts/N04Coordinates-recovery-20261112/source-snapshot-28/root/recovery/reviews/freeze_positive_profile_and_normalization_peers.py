import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = ROOT / 'n04-drafts/quantitative/primitive-route/reconstructed'
OUT = Path(__file__).parent

def ident(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': subprocess.check_output(['git', 'hash-object', str(path)], cwd=REPO).decode().strip(),
            'lines': len(b.splitlines())}

def verify(item):
    actual = ident(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']
    return Path(item['path']).read_text()

def new_source(item, names):
    source = verify(item)
    assert re.findall(r'(?m)^theorem ([^\s]+)', source) == names
    assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', source)
    for name in names:
        r = subprocess.run(['rg', '-l', r'\b' + name + r'\b', 'src/ContinuousFlexibility'], cwd=REPO, capture_output=True)
        assert r.returncode == 1 and not r.stdout

def save(name, data):
    path = OUT / name
    assert not path.exists()
    data['reviewer'] = '/root'
    data['status'] = 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED'
    data['compiled'] = False
    data['reviewed_at'] = datetime.now(timezone.utc).isoformat()
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(ident(path)))

mp = BASE / 'RetainedPositiveComponentProfileLowerCandidateManifest.json'
mi = ident(mp)
assert mi['sha256'] == '16df37fd08b62c938c28be770931c15eabb735d45cdcae2171806037fd00b848'
mf = json.loads(mp.read_text())
new_source(mf['source'], mf['public_names'])
for item in mf['selected_providers'] + mf['new_provider_candidates'] + [
        mf['reviewed_retained_classification'], mf['reviewed_actual_interior_endpoints']]:
    verify(item)
simple_owner = ident(BASE / 'PositiveComponentSimpleProfileLowerReviewedManifest.json')
assert simple_owner['sha256'] == '950192ba62841e50f7edffd4d1526a2e14af74227f5475a2b95fc53a58c182b4'
tail_peer = ident(OUT / 'RetainedPositiveGapProfileLowerIndependentReview.json')
assert tail_peer['sha256'] == '80a5e05c44ea51f2a68c13eb85dca64cceb2ec05669e61419a117f0ab621922e'
save('RetainedPositiveComponentProfileLowerIndependentReview.json', {
    'kind': 'independent_full_source_same_retained_all_positive_component_profile_lower',
    'candidate_manifest': mi, 'source': mf['source'],
    'actual_providers_verified': mf['selected_providers'],
    'new_provider_candidates_verified': mf['new_provider_candidates'],
    'provider_reviews': [simple_owner, tail_peer, mf['reviewed_retained_classification'],
                         mf['reviewed_actual_interior_endpoints']],
    'additional_actual_providers': [ident(REPO / 'src/ContinuousFlexibility/Analysis/MaterialSampleBounds.lean')],
    'read_scope': ['Full122 candidate and its candidate manifest.',
                   'Full117 actual component classification and full121 actual interior endpoint provider.',
                   'Complete simple-profile terminal theorem, actual midpoint definition and core lemma, full65 global endpoint/scaled-floor provider, and the fully reviewed184 tail bound.'],
    'checks': [
        'Every positive component gets its own genuine simple-root lower coefficient, but only the proved finite exceptional set contributes to the common reciprocal maximum. No uniformity is inferred from arbitrary componentwise compactness.',
        'The exception set is exactly the negation of the scaled tail classification. Its finite image of reciprocal coefficients is bounded above even if empty; max1 makes the selected F0 positive.',
        'The actual scaled floor is 1<=K0*E0, with K0>=1 and A>=0. It yields 1<=K0^A*E0^A; B=Bt+F0*K0^A pays for the finite constants without assuming unscaled E0>=1.',
        'The tail case uses the actual left/right equalities and the same physical midpoint to preserve the supplied sample cell. Positive inverse antitonicity weakens its coefficient from Bt to B correctly.',
        'One B and A precede all actual components, midpoint cells and physical points. The same P/Gamma/T/control geometry are retained, including both closed endpoints and the original derivative divided by radius.',
        'All source, candidate and supplied review identities are exact; the two formerly pending provider proofs now have full independent reviews. No public collision, frozen-target change or resource increase is introduced.'
    ],
    'scope_limits': ['This proves a reference physical profile lower, not the final canonical principal bound or any current-state tower.',
                     'No active source/index/ref/compiler/CI changes. The same-Y/H principal consumer remains a separate obligation.']
})

mp = BASE / 'N01OpticalMaterialNormalizationCandidateManifest.json'
mi = ident(mp)
assert mi['sha256'] == '458b3da11f00446154745de46e58426c6be7abd2353f89ccb6b707f29dc1d63a'
mf = json.loads(mp.read_text())
new_source(mf['source'], ['nonlinearPropertiesThrough03_optical_enlargedMaterialData'])
for item in mf['providers'] + [mf['provider_reviewed_manifest']]:
    verify(item)
core_peer = ident(ROOT / 'n04-drafts/audit/reviews/N01ParameterOrderCorePortsIndependentReview.json')
assert core_peer['sha256'] == '95f55482a3bb7e9e7848c3523f078484730fb880bc17b6f80e8424c3e3865a43'
save('N01OpticalMaterialNormalizationIndependentReview.json', {
    'kind': 'independent_full_source_same_witness_optical_material_normalization',
    'candidate_manifest': mi, 'source': mf['source'], 'actual_providers_verified': mf['providers'],
    'provider_reviewed_manifest': mf['provider_reviewed_manifest'], 'provider_independent_review': core_peer,
    'read_scope': ['Full60 candidate, full311 selected envelope normalization provider, actual74 flow/coefficient alias and material sample-membership provider.',
                   'Exact N01/Through03 projections and the reviewed new-main parameter-order selection.'],
    'checks': [
        'The proof applies the real smooth envelope majorant and its established material/physical-space/Through03 transport; D/S/C/R/L/base/loss/radius, samples and H/M remain the same.',
        'The new E0>=1 conclusion is supplied by one_le_enlargedMaterialData_E0 on the entire physical core, rather than inferred from a scaled floor.',
        'The actual sample lies in the core. Both envelopes are positive, original E0<=enlarged E0, and K>0; reciprocal antitonicity therefore makes the enlarged negative-power coefficient smaller.',
        'The endpoint minimum is nonnegative on the actual open control interval, so the same raw optical inequality and the same K survive the multiplication.',
        'No reference atlas, Y/H or interpolation width is selected here; this normalization is available before those dependent choices. The raw optical certificate remains an explicit upstream input and is not projected from Through03.',
        'All source/provider/owner/peer identities are exact, the new public name has no installed collision, and no resource or frozen-contract changes occur.'
    ],
    'scope_limits': ['The selected provider must be installed with the new-main parameter-order cohort. Static review is not a CI result.',
                     'This does not construct the raw optical certificate, a final primitive predicate or a nonzero CurrentJets tower. No active source/index/ref/compiler/CI changes.']
})
