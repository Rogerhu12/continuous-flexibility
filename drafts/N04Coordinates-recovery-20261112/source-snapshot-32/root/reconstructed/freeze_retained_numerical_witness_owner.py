import hashlib, json
from datetime import datetime, timezone
from pathlib import Path

drafts = Path('/workspace/scratch/bbbea77e4163/n04-drafts')
out = drafts / 'root/reconstructed'
def fp(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
        'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
        'lines': len(raw.splitlines())}
candidate = out / 'N04RetainedCorrectionNumericalWitnessCandidateManifest.json'
review = drafts / 'positive/recovery/reviews/N04RetainedCorrectionNumericalWitnessIndependentReview.json'
assert fp(candidate)['sha256'] == '89139f2774b2e4742e9adbd131608b9959f0d8578dd9ce96610d022e20abcace'
assert fp(review)['sha256'] == 'c572743be524a171cd1dab21c0ea874895f114e3d682653ad3279827dc82dfbf'
mf, peer = json.loads(candidate.read_text()), json.loads(review.read_text())
assert peer['result'] == 'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW' and not peer['findings']
for key in ('source','original_reviewed_gateway','original_gateway_source','actual_uniform_provider','actual_N03_record_provider','selected_dependency_graph','exact_retention_specification'):
    row = mf[key]
    actual = fp(row['path'])
    assert all(actual[k] == row[k] for k in ('sha256','blob','lines'))
assert mf['source']['sha256'] == peer['source']['sha256']
owner = {
    'kind': 'same_actual_return_correction_complete_numerical_witness_reviewed_owner',
    'owner': '/root', 'status': 'FULL_SOURCE_INDEPENDENTLY_REVIEWED_HELD_UNCOMPILED',
    'source': mf['source'], 'candidate_manifest': fp(candidate), 'independent_review': fp(review),
    'original_reviewed_gateway': mf['original_reviewed_gateway'],
    'selected_dependency_graph': mf['selected_dependency_graph'],
    'selection': 'Select this new stronger producer exactly once and retain its R,L,chi,host,width and common neighborhood. The immutable old148 witness is not called a second time or equated to an independently selected output.',
    'scope_limits': ['The returned closed-buffer optical lower bound is not a bound on the entire negative component.',
        'Historical selected dependency identities remain unchanged; actual CI160 proof-boundary repairs are tracked independently in CI161.',
        'No final CurrentJets, ReferenceJets or N04Coordinates completion claim; no local compiler or resource override.'],
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()}
path = out / 'N04RetainedCorrectionNumericalWitnessReviewedManifest.json'
assert not path.exists()
path.write_text(json.dumps(owner, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(fp(path)))
