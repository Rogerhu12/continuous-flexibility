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

source = out / 'WholeReferenceGaugeFixedPotentialReferenceJets.lean'
text = source.read_text()
assert not re.search(r'\b(sorry|admit|axiom|opaque)\b|set_option|maxHeartbeats|maxRecDepth|unsafe', text)
assert text.count('theorem n04WholeReferenceGauge_positive_potentialReferenceJets_fixedFamily') == 1
assert 'n04Coordinates_retained_positive_reference' not in text
providers = [
    out / 'FixedPositiveReferencePotentialMaterialJets.lean',
    drafts / 'audit/reconstructed/WholePositiveReferencePotentialJets.lean',
    repo / 'src/ContinuousFlexibility/Analysis/MaterialEnvelopeNormalization.lean',
    drafts / 'audit/reconstructed/WholeReferenceGaugePositivePotentialReferenceJets.lean',
    drafts / 'quantitative/primitive-route/reconstructed/WholeReferenceGaugePositivePrincipalJets.lean',
    Path('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Topology/Neighborhoods.lean'),
    Path('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean')]
assert ident(providers[0])['sha256'] == '0907bd7f6cecbd52a23169516f946964f1a8e46ec97f0f6dc9fb48e64dd0304f'
assert ident(providers[3])['sha256'] == '2b5857a4e63c984a9003ea74eacb6f402ecb48cfc2a0c36f7080aca6aac86112'
assert ident(providers[4])['sha256'] == 'b8e9fe14a443cf93d04a9643633566b731268408fc8ce38131639eced6887540'
owner = out / 'FixedPositiveReferencePotentialMaterialJetsReviewedManifest.json'
assert ident(owner)['sha256'] == '320bf319872bdf8ad8732fb7589f93b9bc664197a71f78765ae06175e425057b'
normpath = 'src/ContinuousFlexibility/Analysis/MaterialEnvelopeNormalization.lean'
old = subprocess.check_output(['git', 'show', '23d28b145e1361fd8c683ba77415226b82be7bb3:' + normpath], cwd=repo, text=True)
new = providers[2].read_text()
def pack_fragment(s):
    start = s.index('theorem coefficientEnvelope_pack')
    return s[start:s.index('/-- Enlarge only the coefficient envelope', start)]
assert pack_fragment(old) == pack_fragment(new)
mf = {
    'kind': 'actual_fixed_positive_reference_potential_atom_adapter',
    'owner': '/root', 'status': 'CANDIDATE_HELD_UNCOMPILED_PENDING_FULL_INDEPENDENT_REVIEW',
    'source': dict(ident(source), target_path='src/ContinuousFlexibility/Analysis/' + source.name),
    'actual_providers_and_patterns': [ident(p) for p in providers],
    'fixed_family_provider_owner': ident(owner),
    'historical_potential_atom_owner': ident(drafts / 'audit/reconstructed/WholeReferenceGaugePositivePotentialReferenceJetsReviewedManifest.json'),
    'principal_atom_owner_for_same_family_contract': ident(drafts / 'quantitative/primitive-route/reconstructed/WholeReferenceGaugePositivePrincipalJetsReviewedManifest.json'),
    'normalization_provider_note': 'The selected main-cohort provider changes unrelated flow-loss wiring. The complete coefficientEnvelope_pack declaration/proof is byte-identical to complete-green CI159.',
    'pack_declaration_sha256': hashlib.sha256(pack_fragment(new).encode()).hexdigest(),
    'public_names': ['n04WholeReferenceGauge_positive_potentialReferenceJets_fixedFamily'],
    'checks': [
        'The entire source was read before freezing. No prior immutable source, active index or ref was modified by this candidate.',
        'Only coefficients M and BM are selected. C0, original cell, Y, H, literal invFun Y, material data T and all geometry are given and remain unchanged.',
        'The hE0 sample floor is supplied on the single actual material normalization before the common family. No further enlargement occurs in the result.',
        'The generic123 scalar bound receives actual height and inverse jets, smoothness from the same range geometry, and the true component inclusion in the fixed compact annulus.',
        'The unit map is exactly the identity on positive canonical pieces with endpoints0/1. Actual141 flux germ yields EqOn for the stored potential; smoothness, pi-periodicity and every mixed derivative transfer through that equality.',
        'One finite prefix coefficient D and coefficientEnvelope_pack are selected before atlas enumeration, transports, piece, spatial point and derivative indices. Sampling is exactly the stored positive cell.',
        'Height and principal adapters can be supplied by one selection of276. This source never invokes that existential producer or any independently selected family.'
    ],
    'scope_limits': [
        'The actual single-selection producer and final ReferenceJets assembly are separate leaves; this is a concrete adapter for the exact supplied family.',
        'This proves the positive potential reference atom only. It does not supply negative potential bounds or quantitative current jets.',
        'Static source review only; no local compiler, resource overrides, CI pass or parent completion claim.'
    ],
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()
}
path = out / 'WholeReferenceGaugeFixedPotentialReferenceJetsCandidateManifest.json'
assert not path.exists()
path.write_text(json.dumps(mf, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': ident(source), 'manifest': ident(path)}))
