import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
mathlib = Path('/workspace/scratch/continuous-flexibility-mathlib')
folder = root / 'n04-drafts/root/recovery/reviews'
candidate = root / 'n04-drafts/audit/reconstructed/ActualNegativeOpticalRootDivisionCandidateManifest.json'

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.splitlines())}

def verify(item):
    actual = identity(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']

assert identity(candidate)['sha256'] == '265e76e881f007d1eaacca85e706d6549b6598abba2c3cb5b876b0ae79e32a58'
manifest = json.loads(candidate.read_text())
for item in [manifest['source'], manifest['new_sample_provider_candidate']] + manifest['provider_refs'] + manifest['provider_reviews'] + manifest['pinned_api_refs']:
    verify(item)
sample_owner_path = root / 'n04-drafts/audit/reconstructed/ActualNegativeHostMaterialSamplesReviewedManifest.json'
assert identity(sample_owner_path)['sha256'] == '7f7be4d881ab4cd071983590d1efdb63532ed0096b5ce17177c5f0e0b1a096e0'
sample_owner = json.loads(sample_owner_path.read_text())
sample_peer = sample_owner['independent_reviews'][0]
verify(sample_peer)
assert sample_peer['sha256'] == '967fb036321aac2b1aac24ebc87c2302077fe366fd02824fcbb434bbb919ff1d'
source = Path(manifest['source']['path']).read_text()
assert not re.search(r'\b(sorry|axiom|unsafe|native_decide)\b|set_option', source)
names = manifest['source']['public_names']
pattern = r'^(theorem|lemma|def|abbrev)\s+(' + '|'.join(map(re.escape, names)) + r')\b'
result = subprocess.run(['rg', '-n', pattern, str(repo / 'src')], capture_output=True, text=True)
assert result.returncode == 1 and not result.stdout, result.stdout
additional = [mathlib / 'Mathlib/Topology/Order/OrderClosed.lean',
              mathlib / 'Mathlib/Algebra/Order/GroupWithZero/Basic.lean',
              mathlib / 'Mathlib/Algebra/Group/Basic.lean']
review = {
    'kind': 'independent_full_source_actual_negative_optical_factor_entire_half',
    'candidate_manifest': identity(candidate),
    'source': manifest['source'],
    'actual_providers_verified': manifest['provider_refs'],
    'provider_reviews_verified': manifest['provider_reviews'],
    'new_sample_provider_owner': identity(sample_owner_path),
    'new_sample_provider_full_peer': sample_peer,
    'pinned_api_refs_verified': manifest['pinned_api_refs'],
    'additional_pinned_actual_providers': [identity(p) for p in additional],
    'read_scope': [
        'Full238 candidate and complete manifest; full154 original smooth optical division, full90 host-to-original-half sample transport, full192 actual radial length bounds, and full90 provider independent review.',
        'Actual negative-component constructor, both negative-half endpoint definitions and inclusion/bounds, exact le_on_closure, le_of_mul_le_mul_left, inv_anti0, div_le_one and inv_div interfaces.'
    ],
    'checks': [
        'For 0<t<d<L the exact min-distance inequality dominates t*(L-d)/L. Cancelling the strictly positive t against the actual F=t*g identity proves the factor lower bound. Continuity extends it to both closed-half endpoints without differentiating an extension.',
        'Both endpoint orientations use inwardComponentPoint exactly. The reciprocal cost is the full physical component width times kappa inverse times the opposite physical half-width inverse; the actual cut lies strictly between the same endpoints.',
        'The true return-margin host supplies both half-width bounds. Its radialE loss is paid at that host sample, then the reviewed90 theorem transfers it to either original stored K.cell sample. There is no cell-identity claim.',
        'The existing154 smooth division is selected once before every derivative order. Its full-component jets and one-derivative division cost survive unchanged; the per-order sample-transfer constants are selected globally before labels, sides, host and point.',
        'The actual kappa inverse equals K0 times E0(hostsample)^K0 and is transferred to the same stored half sample. Only positive E0 is used when powers are inverted or added.',
        'The common physical width is bounded by b-a using the real negative component interior endpoints. It is a fixed positive constant, independent of the component and derivative order.',
        'All candidate/provider and additional sample-owner identities are exact. Three public names have no active collision. No new premise asks for final height, potential or coordinate bounds; no axiom, sorry, unsafe primitive or resource increase appears.'
    ],
    'scope_limits': [
        'The same raw optical lower inequality and genuine component host remain explicit construction inputs. The review does not infer them from arbitrary Through03.',
        'This proves a true entire-half positive factor and reciprocal input. The actual fixed-integral height formula, its material tower and the final potential/current-jet bounds still require downstream proofs.',
        'The90 sample provider was pending when the candidate froze and has since received the exact independently reviewed owner recorded above. The frozen candidate itself remains unchanged.',
        'Static review only; no compiler, CI operation, active source/index/ref mutation or full integration-closure claim.'
    ],
    'reviewer': '/root',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED',
    'compiled': False,
    'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = folder / 'ActualNegativeOpticalRootDivisionIndependentReview.json'
assert not out.exists()
out.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(identity(out)))
