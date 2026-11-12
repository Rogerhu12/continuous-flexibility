import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

r = Path('/workspace/scratch/bbbea77e4163/n04-drafts')
folder = r / 'root/compatibility/n03-preserved-fields'
mf = folder / 'N04PreservedCorrectionWitnessCandidateManifest.json'
peerpath = r / 'positive/recovery/reviews/N04PreservedCorrectionWitnessIndependentReview.json'
def ident(p):
    p = Path(p); b = p.read_bytes()
    return {'path': str(p), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest(),
            'lines': len(b.decode().splitlines())}
candidate = json.loads(mf.read_text())
peer = json.loads(peerpath.read_text())
assert ident(peerpath)['sha256'] == '47aaed608c03fe5cf554a86613c0c7674076b73966d836a163f34bf30d156af9'
assert peer['candidate_manifest'] == ident(mf)
assert peer['sources'] == candidate['sources']
for record in candidate['sources'] + candidate['exact_diffs'] + [peer['selected_main_graph']]:
    actual = ident(record['path'])
    assert all(actual[k] == record[k] for k in ('sha256', 'blob', 'lines'))
owner = {'kind': 'actual_N03_fields_preserved_fixed_witness_reviewed_manifest',
    'owner': '/root', 'status': 'STATIC_REVIEWED_HELD_UNCOMPILED',
    'sources': candidate['sources'], 'candidate_manifest': ident(mf),
    'independent_full_review': ident(peerpath), 'selected_main_graph': peer['selected_main_graph'],
    'scope': 'Retain the same selected correction coefficients/minusFlow/cutoff and real cutoff data alongside Through03. The original public N03 API and all original mathematical construction proofs are preserved. No identity is asserted for an arbitrary existential N03 witness.',
    'compiled': False, 'green_receipt_applies': False,
    'created_at': datetime.now(timezone.utc).isoformat()}
p = folder / 'N04PreservedCorrectionWitnessReviewedManifest.json'
assert not p.exists()
p.write_text(json.dumps(owner, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(p)))
