import ContinuousFlexibility.Analysis.RootInverseNormalizedBounds
import ContinuousFlexibility.Analysis.RootExtensionPhysicalBounds

/-!
# Actual extended root jets from the original flow

The true inverse flow supplies the input of the even and odd root
substitutions. Their ordinary smooth extensions have uniform physical
jets with one fixed additional loss, including the ordinary root jets.
No derivatives of a totalized nonsmooth formula are substituted for the
derivatives of these extensions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local notation "rootOutputBox" =>
  Set.prod (Icc (0 : ℝ) 1) (Icc (-Real.pi) Real.pi)

theorem n04FlowInverse_extendedRoot_fixed_loss
    {Z : Type} [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ Z} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ Λ : ℝ, ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
      ∀ z : Z, p base z ≤ 1 →
      ∀ F : ℝ × N04FlowPoint → ℝ, ContDiff ℝ ∞ F →
      (∀ t v, Function.Periodic (fun θ : ℝ => F (t, (v, θ))) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations F Θ → N04FlowJetBounds p inputLoss A z 1 Λ Θ →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ, |σ| ≤ 1 →
      let G : ℝ × ℝ × ℝ → ℝ :=
        (parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 t q.2)) ∘
          rootFlowNormalizedArgument σ
      ContDiff ℝ ∞ (extendedRootEven G) ∧
        ContDiff ℝ ∞ (extendedRootOddCoefficient G) ∧
        ∀ s : ℕ,
          CSBound s rootOutputBox (extendedRootEven G)
            (B s * (1 + p (s + loss) z)) ∧
          CSBound s rootOutputBox (extendedRootOddCoefficient G)
            (B s * (1 + p (s + loss) z)) := by
  choose CE hCE hEven using exists_csBound_extendedRootEven
  choose CO hCO hOdd using exists_csBound_extendedRootOddCoefficient
  obtain ⟨base, loss, htarget⟩ :=
    n04FlowInverse_normalized_fixed_loss hp hI inputLoss
  refine ⟨base, loss + 1, ?_⟩
  intro A hA Λ
  obtain ⟨D, hD, hnormalized⟩ := htarget A hA Λ
  let B : ℕ → ℝ := fun s => 1 + CE s * D s + CO s * D (s + 1)
  have hCE0 (s : ℕ) : 0 ≤ CE s := zero_le_one.trans (hCE s)
  have hB (s : ℕ) : 0 < B s := by
    exact add_pos (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (hCE0 s) (hD s).le)) (mul_pos (hCO s) (hD (s + 1)))
  refine ⟨B, hB, ?_⟩
  intro z hz F hF hperiod Θ hΘ hforward t ht σ hσ
  let G : ℝ × ℝ × ℝ → ℝ :=
    (parameterizedCircleInverse (fun q : N04FlowPoint => Θ q.1 t q.2)) ∘
      rootFlowNormalizedArgument σ
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_n04FlowInverse hF hperiod hΘ ht).comp (rootFlowNormalizedArgument σ).contDiff
  have hGp (x ζ θ : ℝ) : G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi := by
    simp only [G, Function.comp_apply, rootFlowNormalizedArgument_apply]
    exact parameterizedCircleInverse_period_add Real.pi_ne_zero
      (hforward t ht).1
      (fun q => n04Flow_angular_deriv_pos hF hperiod hΘ ht q.1 q.2)
      (hforward t ht).2.1 (x, σ * ζ) θ
  have hφp : ∀ r, 0 ≤ r → ∀ θ,
      rootEven G (r, θ + Real.pi) = rootEven G (r, θ) + Real.pi :=
    fun r _ θ => rootEven_period_add hGp r θ
  have hχp : ∀ r, 0 ≤ r →
      Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hGp r
  refine ⟨contDiff_extendedRootEven hG Real.pi_ne_zero hφp,
    contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχp, ?_⟩
  intro s
  have hbound (n : ℕ) := hnormalized z hz F hF hperiod Θ hΘ hforward t ht σ hσ n
  have hE := hEven s G hG Real.pi Real.pi_ne_zero hφp
    (D s * (1 + p (s + loss) z)) (hbound s)
  have hO := hOdd s G hG Real.pi Real.pi_ne_zero hχp
    (D (s + 1) * (1 + p (s + 1 + loss) z)) (hbound (s + 1))
  have hEB : CE s * D s ≤ B s := by
    dsimp only [B]
    linarith [mul_nonneg (hCO s).le (hD (s + 1)).le]
  have hOB : CO s * D (s + 1) ≤ B s := by
    dsimp only [B]
    linarith [mul_nonneg (hCE0 s) (hD s).le]
  constructor
  · apply hE.mono_bound
    rw [← mul_assoc]
    exact mul_le_mul hEB
      (add_le_add (le_refl (1 : ℝ)) ((hp (show s + loss ≤ s + (loss + 1) by omega)) z))
      (add_nonneg zero_le_one (apply_nonneg _ _)) (hB s).le
  · apply hO.mono_bound
    rw [← mul_assoc, show s + 1 + loss = s + (loss + 1) by omega]
    exact mul_le_mul_of_nonneg_right hOB
      (add_nonneg zero_le_one (apply_nonneg _ _))

end ContinuousFlexibility.Analysis
