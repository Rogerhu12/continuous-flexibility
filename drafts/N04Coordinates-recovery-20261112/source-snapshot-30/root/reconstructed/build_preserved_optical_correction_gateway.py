import difflib
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
base_dir = root / 'n04-drafts/root/compatibility/n03-preserved-fields'
folder = root / 'n04-drafts/root/compatibility/n03-preserved-optical'
folder.mkdir(parents=True, exist_ok=True)
base_path = base_dir / 'N04FixedCorrectionWitness.lean'

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.splitlines())}

assert identity(base_path)['sha256'] == 'cf0ef6b6b5df83bfe4214f4540ad949e0d95731d92bc65b931e81c6425360bd0'
base = base_path.read_text()
old_name = 'N01Properties.n04_exists_through03_preserving_correction'
new_name = old_name + '_and_discriminant'
begin = base.index('theorem ' + old_name)
header_end = base.index(' := by', begin)
old_header = base[begin:header_end]
conclusion_end = '|iteratedDeriv k (χ m) r| ≤ B * radialE (D.cellIndex (cell m)) ^ Q)'
assert old_header.endswith(conclusion_end)
extra = ''' ∧
          (∀ z ∈ stateNeighborhood S C base' ε', ∀ m (p : PolarPoint),
            p.1 ∈ tsupport (deriv (χ m)) →
              0 < (originalCoefficients D S C z).b p ^ 2 -
                (originalCoefficients D S C z).a p *
                  (originalCoefficients D S C z).c p)'''
strong_header = old_header.replace('theorem ' + old_name, 'theorem ' + new_name, 1) + extra
tail = '\n\nend ContinuousFlexibility.Statements\n'
assert base.endswith(tail)
body = base[header_end:-len(tail)]
old_return = 'hLcoefficients, hLminusFlow, hχ, hχrange, hsupp, hend, hcell, hcutoff⟩'
assert body.count(old_return) == 1
strong_body = body.replace(old_return, old_return[:-1] + ', hdiscFull⟩')
wrapper = ''' := by
  obtain ⟨R, L, χ, cell, base', ε', hbase, hε', hε'ε, hthrough,
    hcoefficients, hminusFlow, hχ, hrange, hsupp, hend, hcell, hjets, _⟩ :=
    hN.n04_exists_through03_preserving_correction_and_discriminant hS hT
  exact ⟨R, L, χ, cell, base', ε', hbase, hε', hε'ε, hthrough,
    hcoefficients, hminusFlow, hχ, hrange, hsupp, hend, hcell, hjets⟩'''
text = base[:begin] + strong_header + strong_body + '\n\n/-- The original fixed-witness interface, retaining the same construction. -/\n' + old_header + wrapper + tail
target = folder / 'N04FixedCorrectionWitness.lean'
assert not target.exists()
target.write_text(text)
assert base_path.read_text() == base
assert text.count(old_header) == 1
assert not re.search(r'\b(sorry|axiom|unsafe|native_decide)\b|set_option', text)
diff = folder / 'N04FixedCorrectionWitness.diff'
diff.write_text(''.join(difflib.unified_diff(base.splitlines(True), text.splitlines(True), fromfile='reviewed117/N04FixedCorrectionWitness.lean', tofile='preserved-optical/N04FixedCorrectionWitness.lean')))
provider = folder / 'ReturnCorrectionUniformNeighborhood.provider.lean.txt'
provider.write_bytes(subprocess.check_output(['git', 'show', 'c5c48d262157a11a76604113c40d2438d480433f:src/ContinuousFlexibility/Analysis/ReturnCorrectionUniformNeighborhood.lean'], cwd=repo))
assert identity(provider)['sha256'] == '6076d8d95cfbc3ddda9c3238ace1f5365f7295cab7840d73a474695db45ad4c6'
mf = {
    'kind': 'fixed_actual_N03_correction_preserves_existing_discriminant',
    'owner': '/root',
    'status': 'CANDIDATE_HELD_UNCOMPILED_PENDING_FULL_INDEPENDENT_REVIEW',
    'source': dict(identity(target), target_path='src/ContinuousFlexibility/Analysis/N04FixedCorrectionWitness.lean'),
    'base': identity(base_path),
    'base_reviewed_manifest': identity(base_dir / 'N04PreservedCorrectionWitnessReviewedManifest.json'),
    'base_independent_review': identity(root / 'n04-drafts/positive/recovery/reviews/N04PreservedCorrectionWitnessIndependentReview.json'),
    'base_selected_graph': identity(root / 'n04-drafts/positive/recovery/reviews/N04PreservedCorrectionWitnessSelectedMainGraph.json'),
    'actual_discriminant_provider': dict(identity(provider), selected_ref='c5c48d262157a11a76604113c40d2438d480433f', target_path='src/ContinuousFlexibility/Analysis/ReturnCorrectionUniformNeighborhood.lean'),
    'actual_N03_record_provider': identity(base_dir / 'N03CorrectionAssembly.lean'),
    'diff': identity(diff),
    'public_names': [new_name, old_name],
    'checks': [
        'The stronger producer retains the same original117 proof through the complete actual return-correction construction, with only hdiscFull added to its final result tuple.',
        'The extra conclusion is the existing original-coefficient discriminant positivity on the tsupport of the very same cutoff derivative, at the very same restricted base and radius. It is quantified over all states in that neighborhood and requires no added stateSector hypothesis.',
        'The exact original public theorem header remains unchanged as a wrapper, discarding only the additional already-proved discriminant clause.',
        'No R/L/chi/cell/reference/material/control witness is reselected in the wrapper. It uses the stronger theorem once and returns the same witnesses.',
        'Imports, local instance name, default options and the original immutable117 source remain unchanged. Select this as a supersession of that one module, never alongside a duplicate provider.'
    ],
    'scope_limits': [
        'This preserves actual construction data; it does not claim full CurrentJets or a final material estimate.',
        'The selected705 main-compatible graph still applies except for the exact one-module source supersession, which needs peer rebinding.',
        'No compiler, CI or active source/index/ref mutation.'
    ],
    'compiled': False,
    'created_at': datetime.now(timezone.utc).isoformat()
}
manifest = folder / 'N04PreservedOpticalCorrectionWitnessCandidateManifest.json'
manifest.write_text(json.dumps(mf, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': identity(target), 'manifest': identity(manifest), 'diff': identity(diff)}))
