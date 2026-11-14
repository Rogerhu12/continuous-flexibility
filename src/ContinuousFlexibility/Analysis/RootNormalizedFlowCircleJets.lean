module

public import ContinuousFlexibility.Analysis.RootNormalizedCircleJets

/-!
# Normalized input jets from the actual controlled root flow

The original ODE and forward estimate give true inverse displacement jets.
The original angular normalization gives its own displacement jets. Both
are combined by the fixed-loss composition estimate, with one low state
order chosen before the component-dependent numerical majorants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local notation "rootInputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Set.prod (Icc (-1 : ℝ) 1) (Icc (-Real.pi) Real.pi))

def N04NormalizedFlowCircleBound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (flowLoss circleLoss low loss : ℕ)
    (A K : ℕ → ℝ) (Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z : E, p low z ≤ 1 →
    ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
    (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
    ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
    N04FlowEquations F Θ → N04FlowJetBounds p flowLoss A z 1 Λ Θ →
    ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
    (∀ (n : ℕ) (θ : ℝ), ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤
      K n * (1 + p (n + circleLoss) z)) →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, |τ| ≤ 1 → ∀ s : ℕ,
      CSBound s rootInputBox
        (h ∘ ((parameterizedCircleInverse
            (fun q : N04FlowPoint => Θ q.1 t q.2)) ∘ rootFlowNormalizedArgument τ))
        (B s * (1 + p (s + loss) z))

theorem n04FlowInverse_normalizedCircle_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (flowLoss circleLoss : ℕ) :
    ∃ low loss : ℕ, ∀ A K : ℕ → ℝ, (∀ n, 0 < A n) → (∀ n, 0 < K n) →
      ∀ Λ : ℝ, ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      N04NormalizedFlowCircleBound p flowLoss circleLoss low loss A K Λ B := by
  obtain ⟨lowI, lossI, hinverse⟩ :=
    n04FlowInverse_displacement_fixed_loss hp hI flowLoss
  obtain ⟨lowC, loss, hcomposition⟩ :=
    rootNormalizedCircleComposition_fixed_loss hp hI (max lossI circleLoss)
  refine ⟨max lowI lowC, loss, ?_⟩
  intro A K hA hK Λ
  obtain ⟨D, hD, hIbound⟩ := hinverse A hA Λ
  let M : ℕ → ℝ := fun n => D n + K n
  have hM (n : ℕ) : 0 < M n := add_pos (hD n) (hK n)
  obtain ⟨B, hB, hCbound⟩ := hcomposition M hM
  refine ⟨B, hB, ?_⟩
  intro z hz F hF hperiod Θ hΘ hforward h hh hcircle t ht τ hτ s
  let g : N04FlowPoint → ℝ :=
    parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 t q.2)
  have hg : ContDiff ℝ ∞ g := contDiff_n04FlowInverse hF hperiod hΘ ht
  have hzI : p lowI z ≤ 1 := ((hp (Nat.le_max_left lowI lowC)) z).trans hz
  have hzC : p lowC z ≤ 1 := ((hp (Nat.le_max_right lowI lowC)) z).trans hz
  have hcirc (n : ℕ) (θ : ℝ) :
      ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤
        M n * (1 + p (n + max lossI circleLoss) z) := by
    apply (hcircle n θ).trans
    exact mul_le_mul (le_add_of_nonneg_left (hD n).le)
      (add_le_add (le_refl (1 : ℝ))
        ((hp (Nat.add_le_add_left (le_max_right lossI circleLoss) n)) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hM n).le
  have hinv (n : ℕ) (q : N04FlowPoint) (hq : q.1 ∈ n04FlowParameterBox) :
      ‖iteratedFDeriv ℝ n (fun y => g y - y.2) q‖ ≤
        M n * (1 + p (n + max lossI circleLoss) z) := by
    apply (hIbound z hzI F hF hperiod Θ hΘ hforward t ht q hq n).trans
    exact mul_le_mul (le_add_of_nonneg_right (hK n).le)
      (add_le_add (le_refl (1 : ℝ))
        ((hp (Nat.add_le_add_left (le_max_left lossI circleLoss) n)) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hM n).le
  exact hCbound z hzC h hh g hg hcirc hinv τ hτ s

end ContinuousFlexibility.Analysis
