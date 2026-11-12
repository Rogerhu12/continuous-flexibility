import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
folder = root / 'n04-drafts/root/recovery/reviews'
candidate = root / 'n04-drafts/quantitative/primitive-route/reconstructed/ReferenceInverseProfileMaterialJetsCandidateManifest.json'

def identity(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.splitlines())}

assert identity(candidate)['sha256'] == '8a2c0e6f690e2499a64d18ee9b22a28dca7fef8df883d5f5148a1bd1d8a91a53'
manifest = json.loads(candidate.read_text())
for item in [manifest['source']] + manifest['actual_providers'] + manifest['selected_provider_reviews']:
    actual = identity(item['path'])
    for key in ('sha256', 'blob', 'lines'):
        assert item[key] == actual[key], (item['path'], key)
source = Path(manifest['source']['path']).read_text()
assert not re.search(r'\b(sorry|axiom|unsafe|native_decide)\b|set_option', source)
assert len(source.splitlines()) == 103
for name in manifest['public_names']:
    assert len(re.findall(r'\btheorem\s+' + re.escape(name) + r'\b', source)) == 1
    for path in (repo / 'src').rglob('*.lean'):
        assert not re.search(r'\b(?:theorem|lemma|def|abbrev)\s+' + re.escape(name) + r'\b', path.read_text())
extra = [repo / 'src/ContinuousFlexibility/Radial/ScaleSlowVariation.lean',
         root / 'n04-drafts/positive/reconstructed/RetainedPositiveComponentInteriorEndpoints.lean']
review = {
    'kind': 'independent_full_source_inverse_profile_material_point_and_same_retained_sample',
    'candidate_manifest': identity(candidate),
    'source': manifest['source'],
    'actual_providers_verified': manifest['actual_providers'],
    'additional_actual_providers': [identity(p) for p in extra],
    'selected_provider_reviews': manifest['selected_provider_reviews'],
    'read_scope': [
        'Full103 candidate and full candidate manifest; full50 actual point radial polynomial, full132 actual endpoint-weight transport, full147 whole-positive endpoint-coordinate transport, and full121 retained interior endpoint proofs.',
        'Actual AccumulatingProfileBounds reciprocal clause and RadialPartition support/partition fields, exists_localizer_ne_zero, radialJet_eq_iteratedDeriv, radialQ_nonneg, and the actual material-sample membership contract.'
    ],
    'checks': [
        'The reciprocal jet comes from the tenth actual accumulating-profile clause. Its original cell and cellIndex are retained; the partition chooses a nonzero localizer at each point and its support lies in that cell.',
        'A=1+sum(C k,k<=N) is positive and dominates each selected C k. Only the genuine radialE=exp(radialQ)>=1 is used for exponent enlargement; no E0>=1 premise appears.',
        'The point50 theorem transfers the resulting fixed radialE power to E0 at that very point. K and P are selected before every point, cell and finite order.',
        'The retained positive component has proved interior endpoints, so its entire closed interval lies in the open radial core where the reciprocal estimates are valid.',
        'The actual whole-interval X estimate compares the original physical point with the original midpoint host sample. The132 weight theorem at gamma=eta=0 removes only zero powers and moves its E0 cost to the same sample.',
        'The final product K*J and exponent A precede all positive components, host indices, closed-interval points and derivative orders. No entire positive component is assumed to lie in its midpoint cell.',
        'Every listed source and review identity is exact. Both new public names are absent from active src. No project axiom, sorry, unsafe proof primitive, target weakening or resource-option increase is introduced.'
    ],
    'scope_limits': [
        'The retained P/Gamma coordinate evidence remains explicit and must come from the fixed actual construction; it is not projected from arbitrary Through03.',
        'The open-core physical reciprocal bound is not an ambient compact reciprocal bound. The four transformed positive principal jet atoms and CurrentJets remain separate obligations.',
        'Static source review only. No compiler, CI query, active source/index/ref mutation, or selected full import-closure claim.'
    ],
    'reviewer': '/root',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED',
    'compiled': False,
    'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = folder / 'ReferenceInverseProfileMaterialJetsIndependentReview.json'
assert not out.exists()
out.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(identity(out)))
