import ContinuousFlexibility.Analysis.RootRescaledMaterialJets

/-!
# A genuine controlled family for the regularized root equation

The independent flow theorem is applied to actual coefficient jets of
the root field. Existence comes from the periodic Picard construction;
joint smoothness and all higher-jet bounds then follow from the flow
theorem. The low state order and loss precede the coefficient constants,
collar, state, material envelope, and chosen solution family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem exists_rootRescaledFlow_fixed_loss
    (hFlow : N04FlowJetsTarget)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ Λ : ℝ, 0 ≤ Λ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) →
      (∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi) →
      (∀ n r, |r| ≤ δ → ∀ θ,
        ‖iteratedFDeriv ℝ n d (r, θ)‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      (∀ n r, |r| ≤ δ → ∀ θ,
        ‖iteratedFDeriv ℝ n c (r, θ)‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
      N04FlowAngularControl (rootRescaledField d c δ) Λ →
      ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRescaledField d c δ) Θ ∧
        N04FlowJetBounds p loss B z W Λ Θ := by
  obtain ⟨base, loss, htarget⟩ := hFlow E p hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA Λ hΛ
  obtain ⟨A', hA', hraw⟩ := rootRescaledField_rawMaterialJets hp inputLoss A hA
  obtain ⟨B, hB, hbound⟩ := htarget A' hA' Λ hΛ
  refine ⟨B, hB, ?_⟩
  intro z hz W hW δ hδ hδone d c hd hc hdperiod hcperiod hdb hcb hcontrol
  obtain ⟨Φ, hinit, hsolve, _, _⟩ := exists_continuous_rootRegularizedFlow
    Real.pi_pos.ne' hd hc hdperiod hcperiod
  let Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ :=
    fun v t θ => Φ (δ * v.1, δ * v.2) t θ
  have heq : N04FlowEquations (rootRescaledField d c δ) Θ := by
    refine ⟨fun v θ => hinit _ θ, ?_⟩
    intro v θ t ht
    exact hsolve (δ * v.1, δ * v.2) θ t ht
  refine ⟨Θ, heq, ?_⟩
  exact hbound z hz W hW (rootRescaledField d c δ)
    (contDiff_rootRescaledField hd hc δ)
    (fun t v => rootRescaledField_periodic hdperiod hcperiod δ t v)
    (hraw z W hW δ hδ hδone d c hd hc hdb hcb) hcontrol Θ heq

end ContinuousFlexibility.Analysis
