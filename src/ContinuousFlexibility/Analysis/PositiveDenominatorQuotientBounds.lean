import ContinuousFlexibility.Analysis.PositiveRootRecoveryBounds

/-!
# Actual quotient jets with a positive denominator

Only the denominator is clamped. The numerator may have either sign.
On a fixed value rectangle this constructs a genuine smooth quotient
extension and bounds its actual derivatives before selecting the state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem exists_smooth_quotient_on_rectangle
    (l₁ u₁ : ℝ) {l₂ u₂ : ℝ} (h₂ : 0 < l₂) (hlu₂ : l₂ ≤ u₂) :
    ∃ Φ : PolarPoint → ℝ, ContDiff ℝ ∞ Φ ∧
      EqOn Φ (fun p => p.1 / p.2) (Icc l₁ u₁ ×ˢ Icc l₂ u₂) ∧
      ∃ D : ℕ → ℝ, ∀ k : ℕ, ∀ q ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂,
        ‖iteratedFDeriv ℝ k Φ q‖ ≤ D k := by
  let C := circleFlowSmoothTimeClamp l₂ u₂ (l₂ / 2) hlu₂ (half_pos h₂)
  have hC : ContDiff ℝ ∞ C := contDiff_circleFlowSmoothTimeClamp hlu₂ (half_pos h₂)
  have hCpos (x : ℝ) : 0 < C x := by
    have hh := (circleFlowSmoothTimeClamp_mem hlu₂ (half_pos h₂) x).1
    change l₂ - l₂ / 2 < C x at hh
    linarith
  let Φ : PolarPoint → ℝ := fun q => q.1 / C q.2
  have hΦ : ContDiff ℝ ∞ Φ :=
    contDiff_fst.div (hC.comp contDiff_snd) (fun q => (hCpos q.2).ne')
  have he : EqOn Φ (fun p => p.1 / p.2) (Icc l₁ u₁ ×ˢ Icc l₂ u₂) := by
    intro q hq
    change q.1 / C q.2 = q.1 / q.2
    rw [show C q.2 = q.2 from circleFlowSmoothTimeClamp_eq hlu₂ (half_pos h₂) hq.2]
  have hK : IsCompact (Icc l₁ u₁ ×ˢ Icc l₂ u₂) := isCompact_Icc.prod isCompact_Icc
  have hbound (k : ℕ) : ∃ D : ℝ, ∀ q ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂,
      ‖iteratedFDeriv ℝ k Φ q‖ ≤ D :=
    hK.exists_bound_of_continuousOn
      (hΦ.continuous_iteratedFDeriv (by simp : (k : ℕ∞ω) ≤ ∞)).continuousOn
  choose D hD using hbound
  exact ⟨Φ, hΦ, he, D, hD⟩

theorem quotient_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∀ l₁ u₁ l₂ u₂ : ℝ, 0 < l₂ → l₂ ≤ u₂ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 →
      ∀ U : Set PolarPoint, IsOpen U →
      ∀ u v : PolarPoint → ℝ,
        ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
        (∀ q ∈ U, (u q, v q) ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂) →
        (∀ q ∈ U, ∀ a b : ℕ, |mixedDerivative a b u q| ≤
          A (a + b) * (1 + p (a + b + inputLoss) z)) →
        (∀ q ∈ U, ∀ a b : ℕ, |mixedDerivative a b v q| ≤
          A (a + b) * (1 + p (a + b + inputLoss) z)) →
        ∀ a b : ℕ, ∀ q ∈ U,
          |mixedDerivative a b (fun y => u y / v y) q| ≤
            B (a + b) * (1 + p (a + b + loss) z) := by
  obtain ⟨base, loss, hclosure⟩ := cylinderPairComposition_fixed_loss_bound hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA l₁ u₁ l₂ u₂ h₂ hlu₂
  obtain ⟨Φ, hΦ, heΦ, D, hD⟩ := exists_smooth_quotient_on_rectangle l₁ u₁ h₂ hlu₂
  obtain ⟨B, hB, hbound⟩ := hclosure A D hA
  refine ⟨B, hB, ?_⟩
  intro z hz U hU u v hu hv hrange hujet hvjet a b q hq
  have hb := hbound z hz U hU u v Φ hu hv hΦ
    (fun y hy k => hD k (u y, v y) (hrange y hy)) hujet hvjet a b q hq
  have he : EqOn (Φ ∘ fun y => (u y, v y)) (fun y => u y / v y) U :=
    fun y hy => heΦ (hrange y hy)
  have hj := mixedDerivative_eqOn_of_isOpen hU he a b hq
  exact (congrArg abs hj).symm.trans_le hb

end ContinuousFlexibility.Analysis
