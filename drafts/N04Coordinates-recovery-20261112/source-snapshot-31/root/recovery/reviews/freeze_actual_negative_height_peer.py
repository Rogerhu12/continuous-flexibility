import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
drafts = root / 'n04-drafts'
mf_path = drafts / 'audit/reconstructed/ActualNegativeReferenceHeightMaterialJetsCandidateManifest.json'

def ident(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

assert ident(mf_path)['sha256'] == 'c978698094452943f73353d8d31f36b9cdd0a6e8d1f23ec62562e8490bc654c1'
mf = json.loads(mf_path.read_text())
records = [mf['source'], *mf['actual_providers'], *mf['reviewed_provider_manifests'], *mf['pinned_api_refs']]
for rec in records:
    now = ident(rec['path'])
    for key in ('sha256', 'blob', 'lines'):
        assert now[key] == rec[key], (rec['path'], key)
source = Path(mf['source']['path']).read_text()
assert not re.search(r'\b(sorry|admit|axiom|opaque|unsafe)\b|set_option|maxHeartbeats|maxRecDepth', source)
public = re.findall(r'^theorem\s+(\S+)', source, re.M)
assert public == mf['source']['public_names']
assert source.count('private theorem ') == 3
collisions = []
for p in (root / 'continuous-flexibility/src').rglob('*.lean'):
    content = p.read_text()
    if any(re.search(r'^(?:theorem|lemma|def)\s+' + re.escape(name) + r'\b', content, re.M) for name in public):
        collisions.append(str(p))
assert not collisions
receipt = {
    'kind': 'same_actual_negative_half_stored_height_material_jets_full_independent_review',
    'reviewer': '/root', 'result': 'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW',
    'candidate_manifest': ident(mf_path), 'source': mf['source'],
    'actual_providers': mf['actual_providers'],
    'reviewed_provider_manifests': mf['reviewed_provider_manifests'],
    'pinned_api_refs': mf['pinned_api_refs'],
    'additional_definitions': [
        ident(drafts / 'quantitative/primitive-route/reconstructed/N01OpticalRootDivision.lean'),
        ident('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean')],
    'read_scope': [
        'All293 source lines and the complete candidate manifest; full151 stored Airy-height equality,131 actual negative sample transport and65 global material floor provider.',
        'The238 actual optical factor,261 all-real-power half-height provider,215 actual average and103 inverse-profile jets were already independently read in full in this task; their exact argument order and relevant interfaces were rechecked.',
        'Pinned translation/reflection iterated-derivative identities, inverse antitonicity, compact derivative bounds and actual inward-coordinate definition were checked. Every manifest fingerprint was recomputed.'
    ],
    'checks': [
        'The first common C0 comes from actual material endpoint models throughout the core, before the real power and piece choices. The raw E0 needs positivity only; no E0>=1 premise is inserted.',
        'All coefficient functions and reciprocal costs are fixed before k,m,side,host,point and angle. The same B(n) controls every true half at the original K.cell k sample.',
        'The238 actual root-division provider supplies a genuine smooth factor g and its exact radicand factorization. The true host j is used only for the optical lower input and is not identified with the stored midpoint sample.',
        'The physical w jets have a compact bound on the closed ambient annulus. Its reciprocal is controlled instead by the103 actual inverse-profile estimate at core points and the131 exact-sample transfer; no compact reciprocal bound at ambient endpoints is used.',
        'Packing from the raw sample to U=C0*E0 uses nonnegative exponents and U>=1, and the single M dominates all coefficient and exponent costs. The g and w value, reciprocal and jet hypotheses of261 are supplied explicitly.',
        'The actual half has positive width and sits inside the closed whole component. One positive smooth c is chosen with the square-root germ on the entire closed half before any x,theta,n. Its average remains the same integral, with no exterior jet or collar-radius bound.',
        'The151 actual stored height equality holds on the full open half for the original K and enumeration. Open EqOn transports every real-power ordinary derivative, including order0; the input c is not reselected per derivative.',
        'The physical-radius corollary reuses the identical C0 and B. The inward map has slope+1 or-1, whose nth absolute power is1. The original k is recovered exactly from e.symm after the explicit index equality.',
        'No final ReferenceJets, CurrentJets, Through04 or coordinate-certificate premise is introduced. Actual raw optical lower provenance remains a separately stated construction obligation.'
    ],
    'findings': [], 'compiled': False, 'source_edited': False,
    'fingerprints_verified': len(records), 'public_collisions': collisions,
    'scope_limits': [
        'These are physical-radius reference height-power estimates for the same actual negative half. Canonical inverse composition, potential and final atom packaging are later consumers.',
        'The uniform raw optical constant and true-host premise must still be produced from the retained construction; this review does not discharge them.',
        'Static full-source review is not Lean elaboration evidence. No compiler, resource overrides, active source/index/ref or CI operation was used for this review.'
    ],
    'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).with_name('ActualNegativeReferenceHeightMaterialJetsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
