import hashlib
import json
import re
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

source = out / 'CanonicalReferenceDividedJets.lean'
text = source.read_text()
assert not re.search(r'\b(sorry|admit|axiom|opaque|unsafe)\b|set_option|maxHeartbeats|maxRecDepth', text)
public = re.findall(r'^theorem\s+(\S+)', text, re.M)
assert public == ['n04bWithInteriorDivision_reference_dividedAtom_zero',
                  'n04bWithInteriorDivision_reference_dividedJets',
                  'n04WholeReferenceGauge_reference_dividedJets']
providers = [out / 'WholeReferenceGaugeAtlasData.lean',
             repo / 'src/ContinuousFlexibility/Analysis/N04bPositiveDivision.lean',
             repo / 'src/ContinuousFlexibility/Statements/Nonlinear.lean',
             repo / 'src/ContinuousFlexibility/Statements/Analysis.lean',
             Path('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean')]
assert ident(providers[0])['sha256'] == '075f99fcadbee80a4b509c417e547dde46e2775898ff540961e65d2f3359eb4a'
collisions = []
for p in (repo / 'src').rglob('*.lean'):
    content = p.read_text()
    if any(re.search(r'^(?:theorem|lemma|def)\s+' + re.escape(name) + r'\b', content, re.M) for name in public):
        collisions.append(str(p))
assert not collisions
mf = {
    'kind': 'actual_reference_divided_atoms_zero_and_all_mixed_material_jets',
    'owner': '/root', 'status': 'CANDIDATE_HELD_UNCOMPILED_PENDING_FULL_INDEPENDENT_REVIEW',
    'source': dict(ident(source), target_path='src/ContinuousFlexibility/Analysis/' + source.name),
    'actual_providers': [ident(p) for p in providers],
    'whole_atlas_provider_owner': ident(out / 'WholeReferenceGaugeAtlasDataReviewedManifest.json'),
    'public_names': public, 'public_collisions': collisions,
    'checks': [
        'The full source and literal quotient/atom/whole-atlas definitions were read before freezing.',
        'At the actual reference state each numerator is a-a; the quotient is therefore0 for every point, including zero denominator. The stored positivity flag then selects0 on both branches.',
        'All three atom functions are globally the zero function. Their smoothness, actual pi-periodicity and every mixed spatial derivative follow from that equality.',
        'B=1 is selected before every piece and atom. Only nonnegativity of the original fixed sample E0 is used; no floor enlargement or geometry assumptions are needed.',
        'The whole reference atlas already ends in n04bWithInteriorDivision. The final adapter merely unfolds this definition and reuses its exact original fields and sampling.',
        'No current-state divided difference is asserted to vanish, and no endpoint extension or final coordinate certificate is used.'
    ],
    'scope_limits': [
        'This supplies the three reference divided atoms only. Quantitative current divided atoms remain a separate boundary-jet and parameter-tower obligation.',
        'Static source review only; no compiler, resource overrides, active source/index/ref mutation or completion claim.'
    ],
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()
}
path = out / 'CanonicalReferenceDividedJetsCandidateManifest.json'
assert not path.exists()
path.write_text(json.dumps(mf, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': ident(source), 'manifest': ident(path)}))
