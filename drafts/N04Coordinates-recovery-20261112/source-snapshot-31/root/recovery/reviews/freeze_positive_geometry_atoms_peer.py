import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
drafts = root / 'n04-drafts'
mf_path = drafts / 'quantitative/primitive-route/reconstructed/WholeReferenceGaugePositiveGeometryJetsCandidateManifest.json'

def ident(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

assert ident(mf_path)['sha256'] == 'c795180d91d5778081abe1a916cf4727e92ad98ff69368a911f244c8674ada22'
mf = json.loads(mf_path.read_text())
records = [mf['source'], *mf['providers'], *mf['provider_owners']]
for rec in records:
    now = ident(rec['path'])
    for key in ('sha256', 'blob', 'lines'):
        assert now[key] == rec[key], (rec['path'], key)
source = Path(mf['source']['path']).read_text()
assert not re.search(r'\b(sorry|admit|axiom|opaque|unsafe)\b|set_option|maxHeartbeats|maxRecDepth', source)
public = re.findall(r'^theorem\s+(\S+)', source, re.M)
assert public == mf['public_names']
collision = subprocess.run(['rg', '-l', '^(theorem|lemma|def)\\s+(' + '|'.join(public) + ')\\b',
                            str(root / 'continuous-flexibility/src')], capture_output=True, text=True)
assert collision.returncode == 1 and not collision.stdout and not collision.stderr
receipt = {
    'kind': 'same_actual_positive_ten_geometry_atoms_full_independent_review',
    'reviewer': '/root', 'result': 'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW',
    'candidate_manifest': ident(mf_path), 'source': mf['source'],
    'providers': mf['providers'], 'provider_owners': mf['provider_owners'],
    'read_scope': [
        'All262 candidate lines and complete candidate manifest; full102 fixed-family material supplier and196 numerical ten-scalar envelope.',
        'Full131 whole-atlas definition and fields; exact171 reference-gauge identity,168 range-geometry fields, literal atom/canonicalSource/unit-point definitions, pinned inverse derivative API and ordinary-to-mixed radial identity.',
        'Exact current coefficientEnvelope_pack declaration and proof. Every source, provider and owner fingerprint independently recomputed; public names checked against installed sources.'
    ],
    'checks': [
        'The same global positive range geometry yields true scalar smoothness of Y,H and the literal invFunY. Its actual nonzero Jacobian and right inverse give chi_prime=1/Y_prime_at_chi; its left inverse gives the reciprocal derivative identity at Y.',
        'The actual physical unit point is l+(r-l)*u, while the positive canonical unit point is exactly(u,theta). The ten full-function equalities preserve this distinction, including JacobianInverse evaluated at the physical point and sourceFactor evaluated at the canonical inverse.',
        'The source is the literal canonicalSource H*f/absJac. Positivity removes the absolute value, and the inverse derivative identity gives H(chi)*chi_prime. Its inverse is reciprocalH(chi)*Y_prime(chi), with signs and factor order checked.',
        'Every displayed scalar is globally smooth from the actual given geometry, including both reciprocal height and derivative-of-inverse factors. Both angle defects are exactly zero; the same radial fields give actual pi-periodicity.',
        'The196 finite envelope handles true zero-order normalized chart and inverse values via real range maps, not an arbitrary inverse-value bound. Its double composition for JacobianInverse and two source products fit C*M^(2N+2), including N=0.',
        'The102 supplier retains the given width and reciprocal-width envelope and all original Y,H,inverse jets. A finite numerical prefix is the only aggregation; no coordinate, interpolation width, cell or height is selected anew.',
        'One BM is obtained before K,e,transports,height ratios,m and points. Exact stored positive metadata determines the original cell, and coefficientEnvelope_pack absorbs C0 only using the explicitly supplied normalized E0>=1.',
        'The inl branch contradicts actual positive metadata and the inr branch uses exact original fields at the reference. The underlying negative atlas is arbitrary and never altered by the positive estimates.',
        'The three public declarations expose only true scalar smoothness, actual full-function equality and the ten reference estimates. No final ReferenceJets, CurrentJets or independently selected family is assumed.'
    ],
    'findings': [], 'compiled': False, 'source_edited': False,
    'fingerprints_verified': len(records), 'public_collisions': [],
    'scope_limits': [
        'Actual once-selected family assembly and the remaining reference scalar columns are separate consumers. Negative estimates and quantitative current jets are not established here.',
        'Static full-source review is not Lean elaboration evidence. No compiler, resource override, active source/index/ref mutation or CI operation was used for the review.'
    ],
    'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).with_name('WholeReferenceGaugePositiveGeometryJetsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
