import ContinuousFlexibility.Analysis.N01ReturnMargins
import ContinuousFlexibility.Analysis.OpticalTravelVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A positive lower bound for the actual optical travel

The frequency-one return margin bounds the positive optical travel from
below at a genuine containing radial cell. This uses only the radial
reference and control geometry, independently of flow differentiation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.travel_nonneg
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    0 ≤ C.travel m := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have htravel : C.travel m = ∫ r in C.left m..C.right m, opticalSpeed D.w r :=
    hcontrol.2.2.2.2.2.2.2.1 m
  rw [htravel]
  exact intervalIntegral.integral_nonneg (hcontrol.1 m).2.1.le
    (fun _ _ => Real.sqrt_nonneg _)

theorem N01Properties.actualCell_travel_lower_bound
    (hN : N01Properties D T S C base loss ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ m,
      0 < C.travel m ∧ ∃ j : ℕ,
        Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        1 ≤ radialE (D.cellIndex j) ^ R * C.travel m := by
  obtain ⟨R, hR, hmargins⟩ := n01Properties_returnMargins hN
  refine ⟨R, hR, fun m => ?_⟩
  obtain ⟨j, hcell, c, hc, hinv, hsmall⟩ := (hmargins m).2
  have hs : c ≤ |Real.sin (C.travel m)| := by
    simpa only [Nat.cast_one, one_mul, div_one] using hsmall 1 (by decide)
  have hcT : c ≤ C.travel m :=
    hs.trans ((Real.abs_sin_le_abs (x := C.travel m)).trans_eq
      (abs_of_nonneg (hN.travel_nonneg m)))
  have hE : 0 < radialE (D.cellIndex j) ^ R := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcE : 1 ≤ radialE (D.cellIndex j) ^ R * c := by
    apply (div_le_iff₀ hc).mp
    simpa only [one_div] using hinv
  exact ⟨hc.trans_le hcT, j, hcell,
    hcE.trans (mul_le_mul_of_nonneg_left hcT hE.le)⟩

end ContinuousFlexibility.Statements
