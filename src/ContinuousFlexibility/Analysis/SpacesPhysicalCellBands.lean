import ContinuousFlexibility.Analysis.SpacesTorusCut
import ContinuousFlexibility.Analysis.SpacesPhysicalFrequencyBands
import ContinuousFlexibility.Analysis.SpacesTorusCellLp
import ContinuousFlexibility.Analysis.SpacesTorusCellCoefficients

/-!
# Actual physical Fourier jet operators in each cell

These operators use the normalized torus only internally. Their inputs
and outputs are the real cylinder `L²` classes fixed in the statements,
and their symbols are the actual physical mixed derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators ComplexConjugate ContDiff

set_option backward.isDefEq.respectTransparency false

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : DecidableEq SpacesTorusFrequency := Classical.decEq _

def spacesPhysicalFourierSymbol (a b : ℕ) (j : SpacesTorusFrequency) : ℂ :=
  spacesUnitFourierSymbol (j 0) (1 / 6) ^ a *
    spacesUnitFourierSymbol (j 1) (1 / Real.pi) ^ b

theorem spacesPhysicalFourierSymbol_zero (j : SpacesTorusFrequency) :
    spacesPhysicalFourierSymbol 0 0 j = 1 := by
  simp only [spacesPhysicalFourierSymbol, pow_zero, one_mul]

theorem spacesPhysicalFourierSymbol_neg (a b : ℕ) (j : SpacesTorusFrequency) :
    spacesPhysicalFourierSymbol a b (-j) = conj (spacesPhysicalFourierSymbol a b j) := by
  have h (q : ℤ) (r : ℝ) : spacesUnitFourierSymbol (-q) r = conj (spacesUnitFourierSymbol q r) := by
    simp only [spacesUnitFourierSymbol, Int.cast_neg, map_mul, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I, map_intCast, mul_neg, neg_mul]
  simp only [spacesPhysicalFourierSymbol, Pi.neg_apply, h, map_mul, map_pow]

theorem spacesPhysicalFourierSymbol_norm (a b : ℕ) (j : SpacesTorusFrequency) :
    ‖spacesPhysicalFourierSymbol a b j‖ =
      (Real.pi / 3 * |(j 0 : ℝ)|) ^ a * (2 * |(j 1 : ℝ)|) ^ b := by
  rw [spacesPhysicalFourierSymbol, norm_mul, norm_pow, norm_pow,
    spacesUnitFourierSymbol_norm, spacesUnitFourierSymbol_norm]
  have hr : |(1 / 6 : ℝ)| * (2 * Real.pi * |(j 0 : ℝ)|) = Real.pi / 3 * |(j 0 : ℝ)| := by
    norm_num
    ring
  have ht : |1 / Real.pi| * (2 * Real.pi * |(j 1 : ℝ)|) = 2 * |(j 1 : ℝ)| := by
    rw [abs_of_pos (one_div_pos.mpr Real.pi_pos)]
    field_simp [Real.pi_ne_zero]
  rw [hr, ht]

/-- Actual cell restriction followed by the normalized torus isometry. -/
def spacesPhysicalCellToTorusL2 (n : ℤ) : CylinderL2 →L[ℝ] SpacesTorusRealL2 :=
  (spacesPhysicalCellToTorus ℝ n).toContinuousLinearMap.comp (spacesCylinderToPhysicalCell ℝ n)

theorem spacesPhysicalCellToTorusL2_apply (n : ℤ) (u : CylinderL2) :
    spacesPhysicalCellToTorusL2 n u =
      spacesPhysicalCellToTorus ℝ n (spacesCylinderToPhysicalCell ℝ n u) := rfl

theorem spacesPhysicalCellToTorusL2_norm_le (n : ℤ) (u : CylinderL2) :
    ‖spacesPhysicalCellToTorusL2 n u‖ ≤ ‖u‖ := by
  rw [spacesPhysicalCellToTorusL2_apply, (spacesPhysicalCellToTorus ℝ n).norm_map]
  exact spacesCylinderToPhysicalCell_norm_le ℝ n u

theorem spacesPhysicalCellToTorusL2_ae (n : ℤ) (u : CylinderL2) :
    (spacesPhysicalCellToTorusL2 n u : SpacesTorus → ℝ) =ᵐ[volume]
      u ∘ spacesPhysicalCellChart n := by
  have hc := (spacesPhysicalCellChart_preserving n).quasiMeasurePreserving.ae_eq_comp
    (spacesCylinderToPhysicalCell_ae ℝ n u)
  exact (spacesPhysicalCellToTorus_ae ℝ n _).trans hc

/-- The finite physical mixed-jet projection, extended by zero off its cell. -/
def spacesPhysicalCellJet (n : ℤ) (S : Finset SpacesTorusFrequency) (a b : ℕ) :
    CylinderL2 →L[ℝ] CylinderL2 :=
  (spacesPhysicalCellToCylinder ℝ n).comp
    ((spacesTorusToPhysicalCell ℝ n).toContinuousLinearMap.comp
      ((spacesTorusRealCut S (spacesPhysicalFourierSymbol a b)).comp (spacesPhysicalCellToTorusL2 n)))

theorem spacesPhysicalCellJet_apply (n : ℤ) (S : Finset SpacesTorusFrequency)
    (a b : ℕ) (u : CylinderL2) :
    spacesPhysicalCellJet n S a b u = spacesPhysicalCellToCylinder ℝ n
      (spacesTorusToPhysicalCell ℝ n (spacesTorusRealCut S (spacesPhysicalFourierSymbol a b)
        (spacesPhysicalCellToTorusL2 n u))) := rfl

theorem spacesPhysicalCellJet_weighted_norm_le (n : ℤ) (S : Finset SpacesTorusFrequency)
    (a b : ℕ) (u : CylinderL2) (w : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j ∈ S, |w| * ‖spacesPhysicalFourierSymbol a b j‖ ≤ C) :
    ‖w • spacesPhysicalCellJet n S a b u‖ ≤ ((6 * Real.pi) ^ (1 / 2 : ℝ) * C) * ‖u‖ := by
  rw [spacesPhysicalCellJet_apply, ← map_smul, ← map_smul]
  have h := spacesTorusRealCut_weighted_norm_le S (spacesPhysicalFourierSymbol a b)
    (spacesPhysicalCellToTorusL2 n u) w hC hbound
  calc
    _ ≤ (6 * Real.pi) ^ (1 / 2 : ℝ) *
        ‖spacesTorusToPhysicalCell ℝ n (w • spacesTorusRealCut S
          (spacesPhysicalFourierSymbol a b) (spacesPhysicalCellToTorusL2 n u))‖ :=
      spacesPhysicalCellToCylinder_norm_le ℝ n _
    _ = (6 * Real.pi) ^ (1 / 2 : ℝ) *
        ‖w • spacesTorusRealCut S (spacesPhysicalFourierSymbol a b) (spacesPhysicalCellToTorusL2 n u)‖ :=
      congrArg ((6 * Real.pi) ^ (1 / 2 : ℝ) * ·) ((spacesTorusToPhysicalCell ℝ n).norm_map _)
    _ ≤ (6 * Real.pi) ^ (1 / 2 : ℝ) * (C * ‖spacesPhysicalCellToTorusL2 n u‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ ((6 * Real.pi) ^ (1 / 2 : ℝ) * C) * ‖u‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spacesPhysicalCellToTorusL2_norm_le n u) hC) (by positivity)

def spacesPhysicalCellBand (n : ℤ) (M : ℝ) (k a b : ℕ) : CylinderL2 →L[ℝ] CylinderL2 :=
  spacesPhysicalCellJet n (spacesPhysicalFrequencyBand M k) a b

theorem spacesPhysicalCellBand_weighted_norm_le (n : ℤ) (M : ℝ) (hM : 1 ≤ M)
    (k a b c s : ℕ) (hord : a + b + c ≤ s) (u : CylinderL2) :
    ‖M ^ c • spacesPhysicalCellBand n M k a b u‖ ≤
      ((6 * Real.pi) ^ (1 / 2 : ℝ) * Real.exp (s : ℝ)) *
        Real.exp ((s : ℝ) * (k : ℝ)) * ‖u‖ := by
  have h := spacesPhysicalCellJet_weighted_norm_le n (spacesPhysicalFrequencyBand M k) a b u
    (M ^ c) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (fun j hj => by
      rw [spacesPhysicalFourierSymbol_norm, abs_of_nonneg (pow_nonneg (zero_le_one.trans hM) c)]
      simpa only [mul_assoc] using spacesPhysicalFrequencyBand_synthesis_bound hM hj a b c s hord)
  simpa only [spacesPhysicalCellBand, mul_assoc] using h

end ContinuousFlexibility.Statements
