import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = Path(__file__).parent

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def identity(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': git('hash-object', str(path)).decode().strip(), 'lines': len(b.splitlines())}

def verify(item):
    if Path(item['path']).is_absolute():
        data = Path(item['path']).read_bytes()
    else:
        data = git('show', item['selected_ref'] + ':' + item['path'])
    assert hashlib.sha256(data).hexdigest() == item['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == item['blob']
    assert len(data.splitlines()) == item['lines']
    return data

mp = BASE / 'N04MinusFirstIntegralCircleCandidateManifest.json'
rp = ROOT / 'n04-drafts/audit/reviews/N04MinusFirstIntegralCircleIndependentReview.json'
mi, ri = identity(mp), identity(rp)
assert mi['sha256'] == 'b4258c87e47a2780763e82b5b0b00d37b642236c5c89da70c926f3a38a4df030'
assert ri['sha256'] == '13d86f28d16191e82fc6d9b0c84ffc70c452cd5e5d486e2f7d1f35ec979ffa1f'
mf, review = json.loads(mp.read_text()), json.loads(rp.read_text())
assert review['candidate_manifest'] == mi and review['source'] == mf['source']
assert review['findings'] == [] and not review['compiled']
for item in [mf['source'], mf['closure_inventory'], mf['selected_input_inventory'],
             review['actual_inverse_reviewed_manifest'], review['actual_inverse_source_review'],
             review['pinned_lean_namespace_api']] + mf['selected_providers'] + review['checked_actual_providers']:
    verify(item)
out = BASE / 'N04MinusFirstIntegralCircleReviewedManifest.json'
assert not out.exists()
owner = {
    'kind': 'reviewed_actual_minus_first_integral_circle_source',
    'status': 'FULL_SOURCE_REVIEWED_HELD_UNCOMPILED',
    'source': mf['source'], 'candidate_manifest': mi, 'independent_review': ri,
    'actual_inverse_reviewed_manifest': review['actual_inverse_reviewed_manifest'],
    'closure_inventory': mf['closure_inventory'],
    'scope': 'Same literal corrected-flow inverse, actual left-chart composition and positive optical-travel affine reconstruction; genuine circle-valued smooth tame family and joint state-angle directional tower at each fixed selected closed radius.',
    'remaining': 'Radial mixed derivatives, moving canonical compositions, uniform sampled height-gain estimates and final CurrentJets remain separate. The historical selected graph has availability checks only and awaits current-main integration and full CI.',
    'compiled': False, 'source_changed_after_review': False,
    'created_at': datetime.now(timezone.utc).isoformat()
}
out.write_text(json.dumps(owner, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(identity(out)))
