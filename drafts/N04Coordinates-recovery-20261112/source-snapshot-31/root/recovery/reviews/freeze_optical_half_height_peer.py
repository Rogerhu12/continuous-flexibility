import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
drafts = root / 'n04-drafts'
mf_path = drafts / 'audit/reconstructed/OpticalHalfAiryHeightMaterialJetsCandidateManifest.json'

def ident(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

assert ident(mf_path)['sha256'] == '224de0c7309f6b1ad4961a4c740df73b26edd0bf715cc93d39cb6d15b91dcbcd'
mf = json.loads(mf_path.read_text())
records = [mf['source'], *mf['actual_providers'], *mf['reviewed_provider_manifests'], *mf['pinned_api_refs']]
for rec in records:
    now = ident(rec['path'])
    for key in ('sha256', 'blob', 'lines'):
        assert now[key] == rec[key], (rec['path'], key)
source = Path(mf['source']['path']).read_text()
assert not re.search(r'\b(sorry|admit|axiom|opaque|unsafe)\b|set_option|maxHeartbeats|maxRecDepth', source)
public = re.findall(r'^theorem\s+(\S+)', source, re.M)
assert public == ['opticalHalf_airyHeight_power_material_jets']
assert source.count('private theorem ') == 3
collisions = []
for p in (root / 'continuous-flexibility/src').rglob('*.lean'):
    if re.search(r'^(?:theorem|lemma|def)\s+opticalHalf_airyHeight_power_material_jets\b', p.read_text(), re.M):
        collisions.append(str(p))
assert not collisions
receipt = {
    'kind': 'same_closed_optical_half_height_all_order_real_power_full_independent_review',
    'reviewer': '/root', 'result': 'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW',
    'candidate_manifest': ident(mf_path), 'source': mf['source'],
    'actual_providers': mf['actual_providers'],
    'reviewed_provider_manifests': mf['reviewed_provider_manifests'],
    'pinned_api_refs': mf['pinned_api_refs'],
    'additional_norm_provider': ident('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean'),
    'read_scope': [
        'All261 candidate lines and the full candidate manifest; complete actual average215, polynomial positive-power137, polynomial product85 and existing N06AiryRadialGerm212.',
        'The exact realGrading interpolation declaration and proof, norm/ordinary iterated derivative conversion, pinned germ derivative equality, local smooth real-power API, nonnegative rpow multiplication and inverse antitonicity APIs.',
        'Every source/provider/owner/API fingerprint in the manifest was independently recomputed. Public names were checked against the active source tree; no compiler was used.'
    ],
    'checks': [
        'The three private reductions specialize the existing genuine polynomial calculus at the zero real state. Each grading value is exactly zero, including the returned loss; the output factor is one, not an assumed uniform state bound.',
        'All numerical functions C,D,S,P,B are selected from a,K,A before E,g,c,w,d,x and derivative order. Adding1 to positive coefficients gives the >=1 bounds needed by subsequent polynomial applications.',
        'At each closed-half point the supplied neighborhood germ c=sqrt(g) transports every ordinary derivative to the real power g^(1/2). Both value and reciprocal use the original positive g bounds and exponents of absolute value at most1.',
        'The true normalized Airy average only samples t*x inside the same closed interval for0<=t<=1. The reviewed215 average preserves V^-1<=c<=V, yields average positivity and reciprocal<=V, and bounds its nth jet by twice the same nth c-jet bound. No exterior c-jet or interval inverse enters.',
        'The slope is exactly c*average^(-1/3). Two real products supply all jets of F=w*slope. F and F^-1 have at most V^3 value cost, including every inverse-factor sign and order; K1=1+K^3+3*K dominates coefficient and exponent of that cost.',
        'At the point F is positive and locally smooth. Continuity gives a genuine positive neighborhood; Real.rpow_mul identifies (F^(-1/2))^a with F^(-a/2) there for every real a. Germ derivative uniqueness therefore transports every height-power jet, including order0 and both closed-half endpoints.',
        'Only g/w value, reciprocal and ordinary jets are quantitative inputs. The theorem does not assume the desired height jets, a smooth extension bound outside the actual half, an inverse localization radius, or new state/coordinate choices.',
        'The proof is also valid for an empty interval; when a point is supplied its nonnegative coordinate is sufficient for all averaging steps. No unmentioned positive interval-width hypothesis is required.'
    ],
    'findings': [], 'compiled': False, 'source_edited': False,
    'fingerprints_verified': len(records), 'public_collisions': collisions,
    'scope_limits': [
        'This is a numerical consequence for the exact supplied optical factor and profile on one physical half. Actual atlas/sample specialization and stored-height germ transfer are still separate consumers.',
        'The raw optical lower premise of the actual factor supplier is not discharged here. CurrentJets, final primitive geometry and the parent theorem are not established by this review.',
        'Static full-source review is not Lean elaboration evidence. No compiler/elaborator, resource overrides, active source/index/ref, CI query or authority mutation was used for this review.'
    ],
    'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).with_name('OpticalHalfAiryHeightMaterialJetsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
