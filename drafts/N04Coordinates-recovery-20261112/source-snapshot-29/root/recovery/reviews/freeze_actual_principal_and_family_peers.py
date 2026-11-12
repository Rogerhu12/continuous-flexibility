import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
DRAFT = ROOT / 'n04-drafts'
Q = DRAFT / 'quantitative/primitive-route/reconstructed'
OUT = DRAFT / 'root/recovery/reviews'

def identity(path):
    p = Path(path)
    data = p.read_bytes()
    return {'path': str(p), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.decode().splitlines())}

def verify(record):
    actual = identity(record['path'])
    for key in ('sha256', 'blob', 'lines'):
        if key in record:
            assert actual[key] == record[key], (record['path'], key, actual[key], record[key])
    return actual

def peer(stem, expected, checks, read_scope):
    mf = Q / (stem + 'CandidateManifest.json')
    data = json.loads(mf.read_text())
    assert data['source']['sha256'] == expected
    source = verify(data['source'])
    providers = [verify(x) for x in data.get('actual_providers', data.get('providers', []))]
    reviews = [verify(x) for x in data.get('selected_provider_reviews', data.get('provider_reviewed_manifests', []))]
    mathlib = [verify(x) for x in data.get('pinned_mathlib_providers', [])]
    text = Path(source['path']).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text)
    assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)', text)
    public = data['public_names']
    for p in (ROOT / 'continuous-flexibility/src').rglob('*.lean'):
        s = p.read_text()
        assert not any(re.search(r'^(?:theorem|def|lemma)\s+' + re.escape(n) + r'\b', s, re.M) for n in public), p
    review = {
        'kind': 'independent_full_source_actual_same_displayed_reference_review',
        'candidate_manifest': identity(mf), 'source': source,
        'actual_providers_verified': providers,
        'provider_reviews_verified': reviews,
        'pinned_mathlib_providers_verified': mathlib,
        'read_scope': read_scope, 'checks': checks,
        'scope_limits': [
            'The same original finite-data certificate is a genuine intermediate producer output, not a final principal or reference-jet target inserted as an assumption.',
            'The retained P/Gamma and the real raw optical/host inputs remain separate construction obligations; no such certificate is projected from arbitrary Through03.',
            'The material datum is fixed before the atlas and displayed family; no identification of independently chosen existential families is made.',
            'Static independent review only. No local compiler or CI claim; active sources, index and refs are untouched.'
        ],
        'reviewer': '/root', 'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED',
        'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
    }
    path = OUT / (stem + 'IndependentReview.json')
    assert not path.exists()
    path.write_text(json.dumps(review, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(identity(path)))

peer('ActualPositiveReferencePrincipalMaterialCost',
     '1f3198433fddcb8aa95c50fe396055d5e69fdde24803291a9c7765f021bbfea6', [
    'Read all194 source lines and matched the literal hfinite certificate with actual allOrder165. C0/B, midpoint cell, source maps, degree n+1, width delta and displayed Y/H are unchanged.',
    'Actual endpoint source160 supplies all13 hypotheses of prescribed148 and cost148. Their projection order gives exactly range geometry, Yprime <= (n+2)U, positive H and Hinv <= 4U^2.',
    'The lower h=(4U^2)^(-1) follows by positive inverse antitonicity from the actual H reciprocal upper bound. The same retained profile122 gives k=(P0*E^A0)^(-1) on the supplied closed physical interval.',
    'M=(n+2)U is positive and M^2/(h^2*k)=16*(n+2)^2*U^6*P0*E^A0. Checked numerator, inverse squares and multiplication powers algebraically.',
    'The actual expansion U^6=B^6*C0^(6B)*E^(6B) uses positive C0/E and pinned Real.rpow_mul_natCast, mul_rpow and rpow_add. No invalid real-power identity for nonpositive bases is used.',
    'The coefficient/exponent pair is fixed before every component, cell and source. The genuine normalized sample bound hE0>=1 is used only by coefficientEnvelope_pack; reviewed normalization60 produces it before choosing the atlas/family.',
    'The final div_le_iff0 multiplication uses the proved positive h^2*k and has the same K*E^K order required by the physical principal criterion.',
    'Source/provider/review SHA256 and Git blob identities all match, public name is absent from active src, and no forbidden proof primitive or resource increase is present.'
], [
    'Full194 candidate and complete candidate manifest.',
    'Full148 prescribed finite factory, full148 same displayed cost factory, full122 actual retained profile lower, full56 reference-family definition.',
    'Actual allOrder165 finite certificate and displayed functions; actual source160 full output fields; complete coefficientEnvelope_pack and pinned real-power/inverse/division interfaces.'
])

peer('ActualPositiveReferencePrescribedFamily',
     '5451e514fc3df2dd89dcd7bfc445abfa8b4c7d8fd46b88095c1ea17fe7cf54f2', [
    'Read all110 lines and full56 N04PositiveReferenceFamily definition. Its three fields are exactly range geometry, coordinate full endpoint jets, and height full endpoint jets through n+1.',
    'The supplied actual cell/hcell and endpoint sources feed hfinite at that same cell. No new C0/B, width, coordinate, height or qualitative reference family is chosen.',
    'Actual source160 supplies all smoothness, endpoint membership, radiality and endpoint value hypotheses; the original hfinite supplies positive slope/height and both finite jet bounds.',
    'Prescribed148 returns the displayed Y/H and the exact three required fields. Endpoint orientation is definitionally n04PositiveEndpoint side = if side then right else left.',
    'At n=3 the certificate has precisely order4, suitable for the existing actual geometry/transmission assembly. It does not assert more than finite endpoint matching.',
    'C0/B positivity need not be added: the consumed hfinite already proves U>=1 at each actual sample. The original material datum is unchanged.',
    'Source/provider/review identities match, public name is absent from active src, and no forbidden proof primitive or resource increase is present.'
], [
    'Full110 candidate and complete candidate manifest.',
    'Full56 actual reference-family definition and full148 prescribed factory.',
    'Actual allOrder165 finite certificate and endpoint source160 output field order; the paired principal194 same-function construction.'
])
