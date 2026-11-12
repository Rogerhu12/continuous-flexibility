import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

drafts = Path('/workspace/scratch/bbbea77e4163/n04-drafts')
out = drafts / 'root/reconstructed'

def ident(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

candidate = out / 'CanonicalReferenceDividedJetsCandidateManifest.json'
review = drafts / 'positive/recovery/reviews/CanonicalReferenceDividedJetsIndependentReview.json'
assert ident(candidate)['sha256'] == '6961f657fc8a7472d07121d063c3d28cb2c63c0bd36a66054bb0885ea4c8dac4'
assert ident(review)['sha256'] == 'adc8a96cc0154a2e7d1a25de1b4f99e185c02336795322d2872df832d8b46270'
mf = json.loads(candidate.read_text())
peer = json.loads(review.read_text())
assert peer['result'] == 'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW'
assert not peer['findings']
for rec in [mf['source'], *mf['actual_providers'], mf['whole_atlas_provider_owner']]:
    now = ident(rec['path'])
    for key in ('sha256', 'blob', 'lines'):
        assert rec[key] == now[key], (rec['path'], key)
assert peer['source']['sha256'] == mf['source']['sha256']
owner = {
    'kind': 'same_actual_reference_divided_atoms_reviewed_owner',
    'status': 'FULL_SOURCE_INDEPENDENTLY_REVIEWED_HELD_UNCOMPILED',
    'candidate_manifest': ident(candidate), 'independent_review': ident(review),
    'source': mf['source'], 'whole_atlas_provider_owner': mf['whole_atlas_provider_owner'],
    'scope': 'The literal stored divided field has three zero reference atom functions. Their smoothness, pi-periodicity and all mixed material jets use the same whole atlas and original sample. No current-state vanishing is asserted.',
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()
}
path = out / 'CanonicalReferenceDividedJetsReviewedManifest.json'
assert not path.exists()
path.write_text(json.dumps(owner, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(path)))
