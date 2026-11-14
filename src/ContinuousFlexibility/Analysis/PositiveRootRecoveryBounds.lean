module

public import ContinuousFlexibility.Analysis.CylinderPairCompositionBounds
public import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fixed-loss recovery of a positive root factor

On a genuine positive value rectangle, the map (H,a) ↦ √H/a has
one fixed globally smooth extension. Compactness bounds its actual
derivatives before the state is chosen. Applying the existing one-high
composition closure therefore does not assume any jets of √H/a.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem exists_smooth_sqrtQuotient_on_rectangle
    {l₁ u₁ l₂ u₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂)
    (hlu₁ : l₁ ≤ u₁) (hlu₂ : l₂ ≤ u₂) :
    ∃ Φ : PolarPoint → ℝ, ContDiff ℝ ∞ Φ ∧
      EqOn Φ (fun p => Real.sqrt p.1 / p.2) (Icc l₁ u₁ ×ˢ Icc l₂ u₂) ∧
      ∃ D : ℕ → ℝ, ∀ k : ℕ, ∀ q ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂,
        ‖iteratedFDeriv ℝ k Φ q‖ ≤ D k := by
  let C₁ := circleFlowSmoothTimeClamp l₁ u₁ (l₁ / 2) hlu₁ (half_pos h₁)
  let C₂ := circleFlowSmoothTimeClamp l₂ u₂ (l₂ / 2) hlu₂ (half_pos h₂)
  have hC₁ : ContDiff ℝ ∞ C₁ :=
    contDiff_circleFlowSmoothTimeClamp hlu₁ (half_pos h₁)
  have hC₂ : ContDiff ℝ ∞ C₂ :=
    contDiff_circleFlowSmoothTimeClamp hlu₂ (half_pos h₂)
  have hC₁pos (x : ℝ) : 0 < C₁ x := by
    have hh := (circleFlowSmoothTimeClamp_mem hlu₁ (half_pos h₁) x).1
    change l₁ - l₁ / 2 < C₁ x at hh
    linarith
  have hC₂pos (x : ℝ) : 0 < C₂ x := by
    have hh := (circleFlowSmoothTimeClamp_mem hlu₂ (half_pos h₂) x).1
    change l₂ - l₂ / 2 < C₂ x at hh
    linarith
  have hC₁eq (x : ℝ) (hx : x ∈ Icc l₁ u₁) : C₁ x = x :=
    circleFlowSmoothTimeClamp_eq hlu₁ (half_pos h₁) hx
  have hC₂eq (x : ℝ) (hx : x ∈ Icc l₂ u₂) : C₂ x = x :=
    circleFlowSmoothTimeClamp_eq hlu₂ (half_pos h₂) hx
  let Φ : PolarPoint → ℝ := fun q => Real.sqrt (C₁ q.1) / C₂ q.2
  have hΦ : ContDiff ℝ ∞ Φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact ((hC₁.contDiffAt.comp q contDiffAt_fst).sqrt (hC₁pos q.1).ne').div
      (hC₂.contDiffAt.comp q contDiffAt_snd) (hC₂pos q.2).ne'
  have he : EqOn Φ (fun p => Real.sqrt p.1 / p.2)
      (Icc l₁ u₁ ×ˢ Icc l₂ u₂) := by
    intro q hq
    change Real.sqrt (C₁ q.1) / C₂ q.2 = Real.sqrt q.1 / q.2
    rw [hC₁eq q.1 hq.1, hC₂eq q.2 hq.2]
  have hK : IsCompact (Icc l₁ u₁ ×ˢ Icc l₂ u₂) := isCompact_Icc.prod isCompact_Icc
  have hbound (k : ℕ) : ∃ D : ℝ, ∀ q ∈ Icc l₁ u₁ ×ˢ Icc l₂ u₂,
      ‖iteratedFDeriv ℝ k Φ q‖ ≤ D :=
    hK.exists_bound_of_continuousOn
      (hΦ.continuous_iteratedFDeriv (by simp : (k : ℕ∞ω) ≤ ∞)).continuousOn
  choose D hD using hbound
  exact ⟨Φ, hΦ, he, D, hD⟩

/-- Actual bounds on the two input fields, and actual positive bounds on
their values, imply all mixed-jet bounds for √H/a. The common low order
and loss are chosen before every value rectangle and derivative order. -/
theorem sqrtQuotient_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∀ l₁ u₁ l₂ u₂ : ℝ, 0 < l₁ → 0 < l₂ → l₁ ≤ u₁ → l₂ ≤ u₂ →
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
          |mixedDerivative a b (fun y => Real.sqrt (u y) / v y) q| ≤
            B (a + b) * (1 + p (a + b + loss) z) := by
  obtain ⟨base, loss, hclosure⟩ := cylinderPairComposition_fixed_loss_bound hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA l₁ u₁ l₂ u₂ h₁ h₂ hlu₁ hlu₂
  obtain ⟨Φ, hΦ, heΦ, D, hD⟩ :=
    exists_smooth_sqrtQuotient_on_rectangle h₁ h₂ hlu₁ hlu₂
  obtain ⟨B, hB, hbound⟩ := hclosure A D hA
  refine ⟨B, hB, ?_⟩
  intro z hz U hU u v hu hv hrange hujet hvjet a b q hq
  have hb := hbound z hz U hU u v Φ hu hv hΦ
    (fun y hy k => hD k (u y, v y) (hrange y hy)) hujet hvjet a b q hq
  have he : EqOn (Φ ∘ fun y => (u y, v y))
      (fun y => Real.sqrt (u y) / v y) U :=
    fun y hy => heΦ (hrange y hy)
  have hj := mixedDerivative_eqOn_of_isOpen hU he a b hq
  exact (congrArg abs hj).symm.trans_le hb

end ContinuousFlexibility.Analysis
