import ContinuousFlexibility.Analysis.N01ControlIndexBound
import ContinuousFlexibility.Analysis.MaterialSampleRadialLoss
import ContinuousFlexibility.Analysis.N01ReturnMargins

/-!
# Uniform return margins from the actual N01 towers

The radial reference provides a small-divisor constant at the actual cell
containing each negative component.  Optical normalization and the two
N01 towers bound that cell's index by the control sample index.  The
actual material endpoint weights absorb the resulting radial loss.

The final margin uses exactly one material sample weight and requires no
identification of the containing cell with the control's weight label.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The complete quantitative bridge: one global constant controls all
actual return small divisors in the material grading sampled at m. -/
theorem N01Properties.uniform_returnMargins
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ,
      QuadraticIrrational (C.travel m / Real.pi) ∧
      ∃ c : ℝ, 0 < c ∧ c⁻¹ ≤ K * T.M (T.sample m) ∧
        ∀ k : ℕ, 1 ≤ k → c / k ≤ |Real.sin (k * C.travel m)| := by
  obtain ⟨R, hR, hmargin⟩ := n01Properties_returnMargins hN
  obtain ⟨A, hA, hindex⟩ := hN.control_actual_cell_index_bound hS hT
  obtain ⟨K, hK, hweight⟩ :=
    materialSample_radialE_rpow_le_M_of_index_bound hT hN.1.1 hA hR.le
  refine ⟨K, hK, fun m => ?_⟩
  obtain ⟨hirr, j, hj, c, hc, hinv, hsine⟩ := hmargin m
  exact ⟨hirr, c, hc, hinv.trans (hweight m (D.cellIndex j) (hindex m j hj)), hsine⟩

/-- A choice of actual positive margins, with a single uniform material
weight bound, suitable for constructing the circle inverse. -/
theorem N01Properties.uniform_returnMargin_family
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 < K ∧ ∃ c : ℕ → ℝ,
      (∀ m, 0 < c m) ∧
      (∀ m, (c m)⁻¹ ≤ K * T.M (T.sample m)) ∧
      ∀ m k : ℕ, 1 ≤ k → c m / k ≤ |Real.sin (k * C.travel m)| := by
  classical
  obtain ⟨K, hK, hm⟩ := hN.uniform_returnMargins hS hT
  choose c hc hinv hsine using fun m => (hm m).2
  exact ⟨K, hK, c, hc, hinv, hsine⟩

end ContinuousFlexibility.Statements
