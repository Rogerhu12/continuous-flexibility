import hashlib
import json
from pathlib import Path

drafts = Path('/workspace/scratch/bbbea77e4163/n04-drafts')
old_path = drafts / 'root/compatibility/n03-preserved-optical/N04FixedCorrectionWitness.lean'
spec_path = drafts / 'positive/recovery/reviews/N04PreservedCorrectionNumericalInputSpecification.json'
assert hashlib.sha256(spec_path.read_bytes()).hexdigest() == '7fe47c4107fc90955485799f115fe9e39c599c6003f91375da9a7b676ea8a5d1'
spec = json.loads(spec_path.read_text())
old = old_path.read_text()
start = old.index('theorem N01Properties.n04_exists_through03_preserving_correction_and_discriminant')
end = old.index('/-- The original fixed-witness interface')
core = old[start:end].strip()
core = core.replace('n04_exists_through03_preserving_correction_and_discriminant',
                    'n04_exists_through03_preserving_correction_numerical_data', 1)
collar = spec['collar_exact_header_fragment']
collar = collar.replace('(∃ j : ℕ → ℕ, ∃ x δ : ℕ → ℝ,', '(∃ x δ : ℕ → ℝ,', 1)
collar = collar.replace('(j m)', '(cell m)')
flow = '''      (∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
          1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧
          deriv (C.minusFlow z m r) θ ≤ 3 / 2) ∧
'''
marker = '                  (originalCoefficients D S C z).c p) := by'
assert core.count(marker) == 1
core = core.replace(marker, marker.removesuffix(' := by') + ' ∧\n' + collar + '\n' +
                    flow + spec['sector_flow_exact_header_fragment'] + ' := by', 1)
core = core.replace('hdiscFull, hcorrected, _, hflow⟩',
                    'hdiscFull, hcorrected, hflowState, hflow⟩', 1)
core = core.replace('⟨j, x, δ, K, Qδ, Qopt, lam, P, _, hQδ, _, hlam, hP,\n    hdata, _, _, hstripSupport, hjets, hpositive⟩',
                    '⟨j, x, δ, K, Qδ, Qopt, lam, P, hK, hQδ, hQopt, hlam, hP,\n    hdata, hformula, hhalfSupport, hstripSupport, hjets, hpositive⟩', 1)
finish = '    hLcoefficients, hLminusFlow, hχ, hχrange, hsupp, hend, hcell, hcutoff, hdiscFull⟩'
assert core.count(finish) == 1
core = core.replace(finish, '''    hLcoefficients, hLminusFlow, hχ, hχrange, hsupp, hend, hcell, hcutoff, hdiscFull,
    ⟨x, δ, K, Qδ, Qopt, lam, P, hK, hQδ, hQopt, hlam, hP,
      hdata, hformula, hhalfSupport, hstripSupport, hjets, hpositive⟩, hflowState, hflow⟩''', 1)
imports = old[:old.index('/-!')]
header = '''/-!
# Retain every numerical witness of the same correction construction

The buffered optical cutoff, its true host and material scales, the
closed-buffer coefficient bounds, and both actual flow slope bounds
are returned with the exact N02/N03 fields produced using them. There is
one invocation of the buffered construction and no second neighborhood
or collar selection after the return correction has been assembled.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

local instance n04NumericalCorrectionStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

'''
source = imports + header + core + '\n\nend ContinuousFlexibility.Statements\n'
assert source.count('hN.exists_opticalCorrection_flow_buffered_uniform hS hT') == 1
assert source.count('obtain ⟨R, hR⟩') == 1
assert source.count('obtain ⟨L, hLcoefficients') == 1
out = Path(__file__).with_name('N04RetainedCorrectionNumericalWitness.lean')
assert not out.exists()
out.write_text(source)
raw = out.read_bytes()
print(json.dumps({'path': str(out), 'sha256': hashlib.sha256(raw).hexdigest(),
                  'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
                  'lines': len(source.splitlines())}))
