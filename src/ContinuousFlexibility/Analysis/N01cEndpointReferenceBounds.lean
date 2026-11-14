module

public import ContinuousFlexibility.Analysis.N01cWholeSpeedPowerBounds
public import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerNormalization

/-!
# The complete endpoint family with a common material constant

All quantifier transport is over an abstract state space. The actual
characteristic-speed wrapper only supplies the genuine whole-speed
control and the component evaluation predicate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem EndpointPowerControl.reference_difference_sameWeight
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (W : EndpointPowerControl p center base loss U Ω δ
      (fun m q => H m q ^ (3 / 4 : ℝ)) E f)
    (hΩ : ∀ m, IsOpen (Ω m))
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    (hcenter : center ∈ U)
    (hunit : ∀ x ∈ U, p base (x - center) ≤ 1)
    (hseg : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (P : I → PolarPoint → Prop) (hP : ∀ m q, P m q → q ∈ Ω m)
    (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a b q, a + b ≤ s → P m q →
      ∃ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun t => f m x t - f m center t) q),
        ∀ x ∈ U, ∀ v : Fin k → X,
          δ m q ^ a * |J.D k x v| ≤
            B * H m q ^ (3 / 4 : ℝ) * E m q ^ B *
              oneHighVariationWeight p base (s + loss) (x - center) v := by
  obtain ⟨C0, A0, hC0, hA0, hb⟩ := W.bounds.difference_oneHigh W.regular hΩ hδ
    (fun m q hq => Real.rpow_nonneg (hH m q hq) _) hE hcenter hunit hseg k s
  obtain ⟨B, hB, hweight⟩ :=
    exists_sameConstant_materialWeight_bound C0 A0 (3 / 4 : ℝ)
  refine ⟨B, hB, ?_⟩
  intro m a b q hab hq
  have hqΩ := hP m q hq
  let J := smoothDirections_mixedDifference (hΩ m) (W.regular m).spatial
    center hcenter a b q hqΩ ((W.regular m).parameter a b q hqΩ)
  refine ⟨J, fun x hx v => ?_⟩
  have hh := hb m a b hab q hqΩ J x hx v
  have hweight' := hweight (H m q) (E m q)
    (oneHighVariationWeight p base (s + loss) (x - center) v)
    (hH m q hqΩ) (hE m q hqΩ)
    (oneHighVariationWeight_nonneg p base (s + loss) (x - center) v)
  simpa only [Real.norm_eq_abs] using hh.trans hweight'


/-- The entire tame quantifier pattern is transported before specializing
the state space. The same zero parameter loss works for the speed family. -/
theorem EndpointPowerControl.reference_difference_tame
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f : I → X → PolarPoint → ℝ}
    (W : EndpointPowerControl p center base loss U Ω δ
      (fun m q => H m q ^ (3 / 4 : ℝ)) E f)
    (hΩ : ∀ m, IsOpen (Ω m))
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    (hcenter : center ∈ U)
    (hunit : ∀ x ∈ U, p base (x - center) ≤ 1)
    (hseg : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, center + t • (x - center) ∈ U)
    (P : I → PolarPoint → Prop) (hP : ∀ m q, P m q → q ∈ Ω m) :
    (∀ x ∈ U, ∀ m, ContDiffOn ℝ ∞ (f m x) (Ω m)) ∧
    ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m a b q, a + b ≤ s → P m q →
      ∃ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun t => f m x t - f m center t) q),
        ∀ x ∈ U, ∀ v : Fin k → X,
          δ m q ^ a * |J.D k x v| ≤
            B * H m q ^ (3 / 4 : ℝ) * E m q ^ B *
              oneHighVariationWeight p base (s + loss + d) (x - center) v := by
  refine ⟨fun x hx m => (W.regular m).spatial x hx, fun k => ⟨0, fun s => ?_⟩⟩
  exact W.reference_difference_sameWeight hΩ hδ hH hE hcenter hunit hseg P hP k s

end ContinuousFlexibility.Analysis
