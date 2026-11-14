import ContinuousFlexibility.Analysis.FixedAngularMultiplierBounds

/-!
# Uniform mixed bounds for the actual sine quotient

Every angle is within pi/4 of a doubled-sine zero. The same fixed smooth
inverse factor works on the larger pi/3 window. The true local formula
and the ordinary angular Taylor estimates therefore cost exactly one or
two angular derivatives, independent of the radial order, evaluation
point, and numerator. No lower bound for the sine is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem exists_near_doubledSine_zero (θ : ℝ) :
    ∃ c : ℝ, Real.sin (2 * c) = 0 ∧
      θ - c ∈ Icc (-(Real.pi / 4)) (Real.pi / 4) := by
  let d : ℝ := Real.pi / 2
  have hd : 0 < d := by dsimp only [d]; positivity
  let n : ℤ := ⌊θ / d + (1 / 2 : ℝ)⌋
  let c : ℝ := (n : ℝ) * d
  have hl : (n : ℝ) ≤ θ / d + 1 / 2 := Int.floor_le _
  have hu : θ / d + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hl' := mul_le_mul_of_nonneg_right hl hd.le
  have hu' := mul_lt_mul_of_pos_right hu hd
  have he : (θ / d + 1 / 2) * d = θ + d / 2 := by
    rw [add_mul, div_mul_cancel₀ _ hd.ne']
    ring
  rw [he] at hl' hu'
  have hlo : c ≤ θ + d / 2 := hl'
  have hup : θ + d / 2 < c + d := by
    simpa only [add_mul, one_mul] using hu'
  have hh : d / 2 = Real.pi / 4 := by dsimp only [d]; ring
  refine ⟨c, ?_, ?_⟩
  · rw [show 2 * c = (n : ℝ) * Real.pi by dsimp only [c, d]; ring,
      Real.sin_int_mul_pi]
  · rw [hh] at hlo hup
    have hd' : d = Real.pi / 2 := rfl
    constructor <;> linarith

/-- The uniform constant precedes the numerator, point and jet bound.
The simple factor costs one derivative, its square two, at every order. -/
theorem exists_angularSineQuotient_mixed_constant (square : Bool) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ F : PolarPoint → ℝ, ContDiff ℝ ∞ F →
        (∀ c : ℝ, Real.sin (2 * c) = 0 → ∀ r : ℝ, F (r, c) = 0) →
        (square = true → ∀ c : ℝ, Real.sin (2 * c) = 0 →
          ∀ r : ℝ, mixedDerivative 0 1 F (r, c) = 0) →
        ∀ p : PolarPoint, ∀ M : ℝ, 0 ≤ M →
          (∀ i j : ℕ, i + j ≤ a + b + sineFactorOrder square → ∀ θ : ℝ,
            |mixedDerivative i j F (p.1, θ)| ≤ M) →
          |mixedDerivative a b (angularSineQuotient square F) p| ≤ C * M := by
  obtain ⟨q, ψ, _, hq0, hqfactor, hqpos, hψ, hψq, _⟩ :=
    exists_doubledSine_factor_and_inverse
  obtain ⟨C, hC, hmult⟩ := exists_fixedAngularMultiplier_constant hψ (sineFactorOrder square) b
  refine ⟨C, hC, ?_⟩
  intro F hF hzero hfirst p M hM hbound
  obtain ⟨c, hc, hp⟩ := exists_near_doubledSine_zero p.2
  have hpwindow : p.2 - c ∈ Ioo (-(Real.pi / 3)) (Real.pi / 3) := by
    constructor <;> linarith [hp.1, hp.2, Real.pi_pos]
  have hG : ContDiff ℝ ∞ (sineFactorTaylor square F c) :=
    contDiff_sineFactorTaylor hF square c
  have hGjets (j : ℕ) (hj : j ≤ b) :
      |mixedDerivative a j (sineFactorTaylor square F c) p| ≤ M := by
    cases square with
    | false =>
        apply abs_mixedDerivative_angularTaylorQuotient_le hF c (hzero c hc) a j
        intro t _
        exact hbound a (j + 1) (by change a + (j + 1) ≤ a + b + 1; omega) _
    | true =>
        apply abs_mixedDerivative_squaredAngularTaylorQuotient_le hF c
          (hzero c hc) (hfirst rfl c hc) a j
        intro t _
        exact hbound a (j + 2) (by change a + (j + 2) ≤ a + b + 2; omega) _
  have hwindow : {y : PolarPoint | y.2 - c ∈
      Ioo (-(Real.pi / 3)) (Real.pi / 3)} ∈ 𝓝 p :=
    (isOpen_Ioo.preimage (continuous_snd.sub continuous_const)).mem_nhds hpwindow
  have he : angularSineQuotient square F =ᶠ[𝓝 p]
      (fun y : PolarPoint => (Real.cos (2 * c) * ψ (y.2 - c)) ^ sineFactorOrder square *
        sineFactorTaylor square F c y) := by
    filter_upwards [hwindow] with y hy
    exact angularSineQuotient_eq_local hq0 hqfactor hqpos hψq hF square c hc
      (hzero c hc) (fun h => hfirst h c hc) hy
  rw [mixedDerivative_eq_of_germ he a b]
  exact hmult c (Real.cos (2 * c)) (Real.abs_cos_le_one _)
    (sineFactorTaylor square F c) hG a p ⟨hpwindow.1.le, hpwindow.2.le⟩ M hM hGjets

end ContinuousFlexibility.Analysis
