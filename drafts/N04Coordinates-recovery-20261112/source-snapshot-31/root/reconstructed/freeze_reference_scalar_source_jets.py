import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
drafts = root / 'n04-drafts'
repo = root / 'continuous-flexibility'
out = drafts / 'root/reconstructed'

def ident(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

source = out / 'FixedReferenceScalarSourceMaterialJets.lean'
text = source.read_text()
assert not re.search(r'\b(sorry|admit|axiom|opaque|unsafe)\b|set_option|maxHeartbeats|maxRecDepth', text)
assert re.findall(r'^theorem\s+(\S+)', text, re.M) == ['fixedReferenceScalarSource_material_jets']
collision = subprocess.run(['rg', '-l', r'^(theorem|lemma|def)\s+fixedReferenceScalarSource_material_jets\b',
                            str(repo / 'src')], capture_output=True, text=True)
assert collision.returncode == 1 and not collision.stdout and not collision.stderr
providers = [
    drafts / 'quantitative/compatibility/principal-envelope-visibility/RadialReferencePotentialJetEnvelope.lean',
    repo / 'src/ContinuousFlexibility/Analysis/N06ReferenceSourceJets.lean',
    repo / 'src/ContinuousFlexibility/Statements/Analysis.lean',
    Path('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean'),
    Path('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean')]
owner = drafts / 'quantitative/compatibility/principal-envelope-visibility/RadialReferencePotentialJetEnvelopeVisibilityReviewedManifest.json'
mf = {
    'kind': 'same_fixed_radial_inverse_and_source_factor_scalar_column_material_jets',
    'owner': '/root', 'status': 'CANDIDATE_HELD_UNCOMPILED_PENDING_FULL_INDEPENDENT_REVIEW',
    'source': dict(ident(source), target_path='src/ContinuousFlexibility/Analysis/' + source.name),
    'actual_providers': [ident(p) for p in providers],
    'numeric_provider_owner': ident(owner),
    'public_names': ['fixedReferenceScalarSource_material_jets'],
    'read_scope': [
        'Complete candidate and complete159 numerical product/composition provider.',
        'Complete unconditional n06_smooth_periodic_angularJets_bounded declaration/proof, mixedDerivative definition, pinned ContDiffWithinAt-to-At and scalar iterated-derivative product identities.'
    ],
    'checks': [
        'X,F,W and physical l,r are fixed inputs. Only A,P,G,CC,CP,M are selected; no coordinate, inverse, height, sample or material normalization is reselected.',
        'Only positive inverse derivatives are quantitative hypotheses. The actual inverse value enters via its genuine compact physical range; no artificial zeroth inverse bound is imposed.',
        'The numerical composition and product envelopes use ContDiffAt at each genuine open-unit point. ContDiffOn is converted using the open interval, so no smooth extension or jet bound outside that interval is assumed.',
        'The fixed radial profile has compact finite-prefix bounds. The fixed angular profile has genuine pi-periodic bounded jets by the unconditional smooth-periodic theorem, without any Through04 or N05 hypothesis.',
        'Separation of radial and angular variables gives the actual mixed derivative exactly. A single s-prefix envelope yields coefficient times (A*W^A)^(s+1), then one M dominates both its nonnegative coefficient and exponent.',
        'M is selected before every family index, point and derivative pair. The result includes actual smoothness and pi-periodicity on the unit strip, as well as all a+b<=s material bounds.',
        'The assumptions are the source factor and inverse jets already produced by the geometry construction. No desired scalar-column bound or final coordinate certificate is assumed.'
    ],
    'scope_limits': [
        'The genuine left and nu column identities, and the positive/negative actual geometry inputs, are separate adapters to this common numerical consequence.',
        'Static source review only; no compiler, resource override, active source/index/ref mutation or completion claim.'
    ],
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()
}
path = out / 'FixedReferenceScalarSourceMaterialJetsCandidateManifest.json'
assert not path.exists()
path.write_text(json.dumps(mf, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': ident(source), 'manifest': ident(path)}))
