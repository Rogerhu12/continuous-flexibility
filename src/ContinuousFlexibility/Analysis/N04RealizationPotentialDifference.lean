module

public import ContinuousFlexibility.Analysis.N04RealizationPotentialOneHigh

/-!
# All parameter orders of the actual potential difference

The positive parameter estimates come from the raw five-field products.
The genuine first derivative on the reference segment supplies order zero.
The same neighborhood, reference state, high seminorm, and original
height gain serve every order in the finite parameter prefix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Raw principal, height, and reciprocal-height jets suffice for the
complete potential difference estimate, including its zeroth jet. -/
theorem n04Realization_potential_difference_oneHigh (k s : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ A : X → SymmetricCoefficients, ∀ H Q : X → PolarPoint → ℝ,
      ∀ RF : ∀ i : Fin 5, MixedJetRegularity U Ω
        (fun x => n04RealizationPotentialInputs (A x) (H x) (Q x) i),
      ∀ W E : PolarPoint → ℝ, ∀ C P : ℝ, 1 ≤ C → 0 ≤ P →
      (∀ q ∈ Ω, 0 ≤ W q ∧ W q ≤ RH ∧ 1 ≤ E q) →
      (∀ i : Fin 5, ∀ j : ℕ, j ≤ max 1 k → ∀ u w : ℕ, u + w ≤ s + 2 →
        ∀ q (hq : q ∈ Ω), ∀ x ∈ U, p base (x - center) ≤ 1 →
        ∀ v : Fin j → X, (∀ t, p base (v t) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
          (∀ t, p high (v t) ≤ R) →
        ‖((RF i).parameter u w q hq).D j x v‖ ≤
          C * E q ^ P * parameterHeightWeight (W q) j *
            R ^ (((u + w : ℕ) : ℝ) / (((s + 2 : ℕ) : ℝ) + 1))) →
      center ∈ U → (∀ x ∈ U, p base (x - center) ≤ 1) →
      (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U) →
      ∀ a b : ℕ, a + b ≤ s → ∀ q (hq : q ∈ Ω),
      ∀ J : SmoothDirections U (fun x => mixedDerivative a b
        (fun z => H x z * divergenceOperator (A x) (Q x) z -
          H center z * divergenceOperator (A center) (Q center) z) q),
      ∀ x ∈ U, ∀ v : Fin k → X,
        ‖J.D k x v‖ ≤ B * C ^ 3 * W q * E q ^ (P * 3) *
          oneHighVariationWeight p base high (x - center) v := by
  obtain ⟨B, hB, hb⟩ := n04Realization_potential_positive_oneHigh (X := X) (max 1 k) s RH
  refine ⟨2 * B, mul_pos (by norm_num) hB, ?_⟩
  intro p center base high U hU Ω hΩ A H Q RF W E C P hC hP hweight hraw
    hcenter hlow hsegment a b hab q hq J x hx v
  let f : X → PolarPoint → ℝ := fun y z => H y z * divergenceOperator (A y) (Q y) z
  let RP : MixedJetRegularity U Ω f := (RF 0).mul
    (n04Realization_mixedJetRegularity_divergence hU hΩ (RF 1) (RF 2) (RF 3) (RF 4))
    hU hΩ
  let J0 : SmoothDirections U (fun y => mixedDerivative a b (f y) q) :=
    RP.parameter a b q hq
  let JD : SmoothDirections U
      (fun y => mixedDerivative a b (f y) q - mixedDerivative a b (f center) q) :=
    J.congr (fun y hy => mixedDerivative_sub_of_contDiffOn hΩ
      (RP.spatial y hy) (RP.spatial center hcenter) a b hq)
  let M : ℝ := B * C ^ 3 * W q * E q ^ (P * 3)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg hB.le (pow_nonneg (zero_le_one.trans hC) _))
      (hweight q hq).1) (Real.rpow_nonneg (zero_le_one.trans (hweight q hq).2.2) _)
  have hbound := smoothDirections_difference_allOrders_bound J0 p base high center x
    hx (hsegment x hx) (hlow x hx) hM
    (fun j hj hjpos y hy w => hb p center base high U hU Ω hΩ A H Q RF
      W E C P hC hP hweight hraw j hj hjpos a b hab q hq J0 y hy (hlow y hy) w)
    JD v
  simpa only [JD, SmoothDirections.congr, M, mul_assoc] using hbound

end ContinuousFlexibility.Analysis
