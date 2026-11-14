module

public import ContinuousFlexibility.Analysis.N04RealizationPotentialOneHigh
public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue

/-!
# The potential value difference has no additive constant

Only the raw five-field parameter prefix through order one is used. The
genuine first derivative on the same reference segment gives precisely
the displacement factor required by the zeroth current-jet clause.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Raw jets through the first parameter order give a potential value
difference proportional to the high seminorm of the displacement. -/
theorem n04Realization_potential_difference_value_bound (s : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ), p base ≤ p high →
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ A : X → SymmetricCoefficients, ∀ H Q : X → PolarPoint → ℝ,
      ∀ RF : ∀ i : Fin 5, MixedJetRegularity U Ω
        (fun x => n04RealizationPotentialInputs (A x) (H x) (Q x) i),
      ∀ W E : PolarPoint → ℝ, ∀ C P : ℝ, 1 ≤ C → 0 ≤ P →
      (∀ q ∈ Ω, 0 ≤ W q ∧ W q ≤ RH ∧ 1 ≤ E q) →
      (∀ i : Fin 5, ∀ j : ℕ, j ≤ 1 → ∀ u w : ℕ, u + w ≤ s + 2 →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
          (∀ t, p high (v t) ≤ R) →
        ‖((RF i).parameter u w q hq).D j x v‖ ≤
          C * E q ^ P * parameterHeightWeight (W q) j *
            R ^ (((u + w : ℕ) : ℝ) / (((s + 2 : ℕ) : ℝ) + 1))) →
      center ∈ U → (∀ x ∈ U, p base (x - center) ≤ 1) →
      (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U) →
      ∀ a b : ℕ, a + b ≤ s → ∀ q ∈ Ω, ∀ x ∈ U,
        |mixedDerivative a b
          (fun z => H x z * divergenceOperator (A x) (Q x) z -
            H center z * divergenceOperator (A center) (Q center) z) q| ≤
          B * C ^ 3 * W q * E q ^ (P * 3) * p high (x - center) := by
  obtain ⟨B, hB, hb⟩ := n04Realization_potential_positive_oneHigh (X := X) 1 s RH
  refine ⟨3 * B, mul_pos (by norm_num) hB, ?_⟩
  intro p center base high horder U hU Ω hΩ A H Q RF W E C P hC hP hweight hraw
    hcenter hlow hsegment a b hab q hq x hx
  let f : X → PolarPoint → ℝ := fun y z => H y z * divergenceOperator (A y) (Q y) z
  let RP : MixedJetRegularity U Ω f := (RF 0).mul
    (n04Realization_mixedJetRegularity_divergence hU hΩ (RF 1) (RF 2) (RF 3) (RF 4))
    hU hΩ
  let J0 : SmoothDirections U (fun y => mixedDerivative a b (f y) q) :=
    RP.parameter a b q hq
  let M : ℝ := B * C ^ 3 * W q * E q ^ (P * 3)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg hB.le (pow_nonneg (zero_le_one.trans hC) _))
      (hweight q hq).1) (Real.rpow_nonneg (zero_le_one.trans (hweight q hq).2.2) _)
  have hh := n04Realization_smoothDirections_difference_value_bound J0 p base high
    center (x - center) horder (hsegment x hx) (hlow x hx) hM
    (fun y hy v => by
      simpa only [Real.norm_eq_abs] using hb p center base high U hU Ω hΩ A H Q RF
        W E C P hC hP hweight hraw 1 le_rfl zero_lt_one a b hab q hq J0 y hy (hlow y hy) v)
  have hxcenter : center + (x - center) = x := by abel
  rw [mixedDerivative_sub_of_contDiffOn hΩ (RP.spatial x hx)
    (RP.spatial center hcenter) a b hq]
  simpa only [hxcenter, M, mul_assoc] using hh

end ContinuousFlexibility.Analysis
