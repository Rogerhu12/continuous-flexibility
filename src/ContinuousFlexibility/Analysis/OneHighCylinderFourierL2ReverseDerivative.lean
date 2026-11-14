module

public import ContinuousFlexibility.Analysis.OneHighCylinderFourierL2Derivative

/-!
# Frequency regularity gives actual derivative membership

If a continuous classical derivative has a square-integrable Fourier
multiplier, it is square integrable. The inverse L2 transform supplies a
candidate weak derivative. Compact smooth tests and integration by parts
identify that candidate with the given actual derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory SchwartzMap Filter
open scoped ENNReal FourierTransform SchwartzMap ContDiff

theorem real_l2_fourierInv_pairing (g : Lp ℂ 2 (volume : Measure ℝ)) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, φ x * (𝓕⁻ g : Lp ℂ 2 (volume : Measure ℝ)) x) =
      ∫ ξ : ℝ, (𝓕⁻ φ) ξ * g ξ := by
  symm
  simpa only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] using
    congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ) (Lp.fourierInv_toTemperedDistribution_eq g)

/-- Compact support of the test function permits a merely continuous
actual derivative; its global L2 membership is not assumed. -/
theorem real_l2_integral_mul_deriv_compact (u v : ℝ → ℂ)
    (hu : MemLp u 2 (volume : Measure ℝ)) (hv : Continuous v)
    (hderiv : ∀ x : ℝ, HasDerivAt u (v x) x)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    (∫ x : ℝ, φ x * v x) =
      - ∫ x : ℝ, SchwartzMap.derivCLM ℂ ℂ φ x * u x := by
  have hφv : Integrable ((φ : ℝ → ℂ) * v) :=
    (φ.continuous.mul hv).integrable_of_hasCompactSupport hφ.mul_right
  have hdφu : Integrable ((SchwartzMap.derivCLM ℂ ℂ φ : ℝ → ℂ) * u) :=
    memLp_one_iff_integrable.mp (((SchwartzMap.derivCLM ℂ ℂ φ).memLp 2).mul hu)
  have hφu : Integrable ((φ : ℝ → ℂ) * u) :=
    memLp_one_iff_integrable.mp ((φ.memLp 2).mul hu)
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => φ.hasDerivAt x) (fun x _ => hderiv x) hφv hdφu hφu

/-- Membership of the actual first derivative follows from membership of
the physical frequency multiplier. No integrability of that derivative is
a hypothesis. -/
theorem real_memLp_derivative_of_frequency (u v : ℝ → ℂ)
    (hu : MemLp u 2 (volume : Measure ℝ)) (hv : Continuous v)
    (hderiv : ∀ x : ℝ, HasDerivAt u (v x) x)
    (hM : MemLp (fun ξ : ℝ => (2 * Real.pi * Complex.I) * (ξ : ℂ) *
      (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) ξ) 2 (volume : Measure ℝ)) :
    MemLp v 2 (volume : Measure ℝ) := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hu.toLp u)
  let c : ℂ := 2 * Real.pi * Complex.I
  let M : ℝ → ℂ := fun ξ => c * (ξ : ℂ) * F ξ
  change MemLp M 2 (volume : Measure ℝ) at hM
  let V : Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ (hM.toLp M)
  have he : (V : ℝ → ℂ) =ᵐ[volume] v := by
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp V).locallyIntegrable (by norm_num)) hv.locallyIntegrable
    intro a ha hcompact
    have hac : HasCompactSupport (Complex.ofRealCLM ∘ a) := hcompact.comp_left rfl
    have has : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ a) := Complex.ofRealCLM.contDiff.comp ha
    let φ : 𝓢(ℝ, ℂ) := hac.toSchwartzMap has
    have hφcoe : (φ : ℝ → ℂ) = Complex.ofRealCLM ∘ a := by
      funext x
      rfl
    have hφ : HasCompactSupport (φ : ℝ → ℂ) := by
      rw [hφcoe]
      exact hac
    let η : 𝓢(ℝ, ℂ) :=
      c • SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => ξ) (𝓕⁻ φ)
    have hgrowth : (fun ξ : ℝ => ξ).HasTemperateGrowth := by fun_prop
    have hη (ξ : ℝ) : η ξ = c * (ξ : ℂ) * (𝓕⁻ φ) ξ := by
      simp [η, SchwartzMap.smulLeftCLM_apply_apply hgrowth, Complex.real_smul,
        smul_eq_mul, mul_assoc]
    have hd : SchwartzMap.derivCLM ℂ ℂ φ = -𝓕 η := by
      simpa only [FourierTransform.fourier_fourierInv_eq] using
        real_schwartz_deriv_fourier (𝓕⁻ φ)
    have hp : (∫ x : ℝ, φ x * V x) = ∫ x : ℝ, φ x * v x := by
      calc
        _ = ∫ ξ : ℝ, (𝓕⁻ φ) ξ * hM.toLp M ξ :=
          real_l2_fourierInv_pairing (hM.toLp M) φ
        _ = ∫ ξ : ℝ, η ξ * F ξ := by
          apply integral_congr_ae
          filter_upwards [hM.coeFn_toLp] with ξ hξ
          rw [hξ, hη]
          dsimp only [M]
          ring
        _ = ∫ x : ℝ, (𝓕 η) x * u x := real_l2_fourier_pairing u hu η
        _ = - ∫ x : ℝ, SchwartzMap.derivCLM ℂ ℂ φ x * u x := by
          rw [hd]
          simp only [SchwartzMap.neg_apply, neg_mul, integral_neg, neg_neg]
        _ = ∫ x : ℝ, φ x * v x :=
          (real_l2_integral_mul_deriv_compact u v hu hv hderiv φ hφ).symm
    simpa [φ, Complex.real_smul, smul_eq_mul] using hp
  exact (memLp_congr_ae he).mp (Lp.memLp V)

end ContinuousFlexibility.Analysis
