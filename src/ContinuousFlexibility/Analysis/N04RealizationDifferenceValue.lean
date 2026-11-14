import ContinuousFlexibility.Analysis.N01cReferenceDifferenceBounds

/-!
# A reference difference vanishes with its displacement

If the high seminorm dominates the low seminorm, the one-high first-jet
weight on the reference segment is at most three times the high
seminorm of the displacement. No additive constant is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The first-jet segment weight has no constant term when the high
seminorm controls the low seminorm. -/
theorem n04Realization_oneHigh_segment_displacement_bound
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (center d : X)
    (horder : p base ≤ p high) (hlow : p base d ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    oneHighVariationWeight p base high ((center + t • d) - center)
      (Fin.cons d Fin.elim0 : Fin 1 → X) ≤ 3 * p high d := by
  have hdiff : (center + t • d) - center = t • d := by abel
  have hscale : p high (t • d) ≤ p high d := by
    rw [map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (apply_nonneg _ _) ht.2
  have hformula :
      oneHighVariationWeight p base high ((center + t • d) - center)
        (Fin.cons d Fin.elim0 : Fin 1 → X) =
        (1 + p high (t • d)) * p base d + p high d := by
    rw [hdiff]
    simp [oneHighVariationWeight]
  rw [hformula]
  have hprod : p high (t • d) * p base d ≤ p high d :=
    (mul_le_mul_of_nonneg_right hscale (apply_nonneg _ _)).trans
      (mul_le_of_le_one_right (apply_nonneg _ _) hlow)
  nlinarith [horder d]

/-- The genuine scalar first derivative controls the value difference
by the displacement alone, keeping every external material factor. -/
theorem n04Realization_smoothDirections_difference_value_bound
    {U : Set X} {f : X → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (center d : X)
    (horder : p base ≤ p high)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, center + t • d ∈ U)
    (hlow : p base d ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hfirst : ∀ y ∈ U, ∀ v : Fin 1 → X,
      |J.D 1 y v| ≤ M * oneHighVariationWeight p base high (y - center) v) :
    |f (center + d) - f center| ≤ (3 * M) * p high d := by
  apply smoothDirections_abs_sub_le_of_firstJet_bound J hsegment
  intro t ht
  calc
    _ ≤ M * oneHighVariationWeight p base high ((center + t • d) - center)
        (Fin.cons d Fin.elim0 : Fin 1 → X) :=
      hfirst (center + t • d) (hsegment t ht) _
    _ ≤ M * (3 * p high d) := mul_le_mul_of_nonneg_left
      (n04Realization_oneHigh_segment_displacement_bound p base high center d horder hlow ht) hM
    _ = _ := by ring

end ContinuousFlexibility.Analysis
