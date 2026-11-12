import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# A common scale for a finite parameter prefix

An extra interpolation cost proportional to the parameter order can be
removed from every input block by rescaling its directions once. The
same rescaling on the genuine output restores that cost only once, at
the total parameter order. No low seminorm is changed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

/-- Change the interpolation denominator without requesting any extra
spatial derivatives from the source family. -/
theorem n04Realization_rpow_change_budget {R : ℝ} (hR : 0 ≤ R)
    {A : ℝ} (hA : A ≠ 0) (B n : ℝ) :
    (R ^ (A / B)) ^ (n / A) = R ^ (n / B) := by
  rw [← Real.rpow_mul hR]
  congr 1
  calc
    A / B * (n / A) = (A / A) * (n / B) := by ring
    _ = n / B := by rw [div_self hA, one_mul]

variable {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ}

theorem n04Realization_parameter_rescale_norm
    (A : X [×k]→L[ℝ] Y) (v : Fin k → X) {R : ℝ} (hR : 0 < R) (α : ℝ) :
    ‖A (fun i => R ^ (-α) • v i)‖ = R ^ (-α * (k : ℝ)) * ‖A v‖ := by
  rw [A.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (pow_pos (Real.rpow_pos_of_pos hR _) _),
    ← Real.rpow_mul_natCast hR.le]

/-- The same scalar removes the order cost from every partition block. -/
theorem n04Realization_parameter_rescale_bound
    (A : X [×k]→L[ℝ] Y) (v : Fin k → X) {R : ℝ} (hR : 0 < R)
    (α β M : ℝ) (hbound : ‖A v‖ ≤ M * R ^ (β + α * (k : ℝ))) :
    ‖A (fun i => R ^ (-α) • v i)‖ ≤ M * R ^ β := by
  rw [n04Realization_parameter_rescale_norm A v hR α]
  calc
    _ ≤ R ^ (-α * (k : ℝ)) * (M * R ^ (β + α * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hR.le _)
    _ = M * (R ^ (-α * (k : ℝ)) * R ^ (β + α * (k : ℝ))) := by ring
    _ = M * R ^ (-α * (k : ℝ) + (β + α * (k : ℝ))) := by
      rw [Real.rpow_add hR]
    _ = M * R ^ β := by congr 2; ring

/-- Restore the parameter cost after estimating the complete output. -/
theorem n04Realization_parameter_unscale_bound
    (A : X [×k]→L[ℝ] Y) (v : Fin k → X) {R : ℝ} (hR : 0 < R)
    (α β M : ℝ)
    (hbound : ‖A (fun i => R ^ (-α) • v i)‖ ≤ M * R ^ β) :
    ‖A v‖ ≤ M * R ^ (β + α * (k : ℝ)) := by
  have heq : ‖A v‖ = R ^ (α * (k : ℝ)) *
      ‖A (fun i => R ^ (-α) • v i)‖ := by
    rw [n04Realization_parameter_rescale_norm A v hR α, ← mul_assoc,
      ← Real.rpow_add hR]
    rw [show α * (k : ℝ) + -α * (k : ℝ) = 0 by ring,
      Real.rpow_zero, one_mul]
  calc
    _ = R ^ (α * (k : ℝ)) * ‖A (fun i => R ^ (-α) • v i)‖ := heq
    _ ≤ R ^ (α * (k : ℝ)) * (M * R ^ β) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hR.le _)
    _ = M * (R ^ β * R ^ (α * (k : ℝ))) := by ring
    _ = M * R ^ (β + α * (k : ℝ)) := by rw [Real.rpow_add hR]

end ContinuousFlexibility.Analysis
