module

public import ContinuousFlexibility.Analysis.OneHighCylinderFourierL2Inversion
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual radial derivatives under the `L²` Fourier transform

Integration by parts against Schwartz functions requires only `L²`
membership of the function and its actual derivative. Hölder supplies all
three product integrability conditions, so no boundary decay or physical
`L¹` hypothesis is added. The Fourier multiplier identity follows by
testing against compactly supported smooth functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory SchwartzMap Filter LineDeriv
open scoped ENNReal FourierTransform SchwartzMap ContDiff

/-- The actual `L²` Fourier transform has the classical bilinear pairing
with every Schwartz test function. -/
theorem real_l2_fourier_pairing (u : ℝ → ℂ) (hu : MemLp u 2 (volume : Measure ℝ))
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, φ ξ * (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) ξ) =
      ∫ x : ℝ, (𝓕 φ) x * u x := by
  have ht : (∫ x : ℝ, (𝓕 φ) x * hu.toLp u x) =
      ∫ ξ : ℝ, φ ξ * (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) ξ := by
    simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] using
      congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ) (Lp.fourier_toTemperedDistribution_eq (hu.toLp u))
  exact ht.symm.trans (integral_congr_ae (hu.coeFn_toLp.mono fun x hx => by
    dsimp only
    rw [hx]))

/-- Integration by parts for an actual `L²` derivative and an arbitrary
Schwartz test function. -/
theorem real_l2_integral_mul_deriv (u v : ℝ → ℂ)
    (hu : MemLp u 2 (volume : Measure ℝ)) (hv : MemLp v 2 (volume : Measure ℝ))
    (hderiv : ∀ x : ℝ, HasDerivAt u (v x) x) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, φ x * v x) =
      - ∫ x : ℝ, SchwartzMap.derivCLM ℂ ℂ φ x * u x := by
  have hφv : Integrable ((φ : ℝ → ℂ) * v) :=
    memLp_one_iff_integrable.mp ((φ.memLp 2).mul hv)
  have hdφu : Integrable ((SchwartzMap.derivCLM ℂ ℂ φ : ℝ → ℂ) * u) :=
    memLp_one_iff_integrable.mp (((SchwartzMap.derivCLM ℂ ℂ φ).memLp 2).mul hu)
  have hφu : Integrable ((φ : ℝ → ℂ) * u) :=
    memLp_one_iff_integrable.mp ((φ.memLp 2).mul hu)
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => φ.hasDerivAt x) (fun x _ => hderiv x) hφv hdφu hφu

theorem real_schwartz_deriv_fourier (φ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.derivCLM ℂ ℂ (𝓕 φ) =
      -𝓕 ((2 * Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => ξ) φ) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ (𝓕 φ) = lineDerivOp (1 : ℝ) (𝓕 φ) := by
    ext x
    rw [SchwartzMap.derivCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [hd, SchwartzMap.lineDerivOp_fourier_eq]
  have hi : (fun ξ : ℝ => inner ℝ ξ (1 : ℝ)) = fun ξ : ℝ => ξ := by
    funext ξ
    simp
  rw [hi, neg_smul, FourierTransform.fourier_neg]

/-- The Fourier transform of an actual square-integrable derivative is
the physical radial frequency multiplier times the original actual
`L²` Fourier transform, almost everywhere. -/
theorem real_l2_fourier_derivative_ae (u v : ℝ → ℂ)
    (hu : MemLp u 2 (volume : Measure ℝ)) (hv : MemLp v 2 (volume : Measure ℝ))
    (hderiv : ∀ x : ℝ, HasDerivAt u (v x) x) :
    ((𝓕 (hv.toLp v) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (2 * Real.pi * Complex.I) * (ξ : ℂ) *
        (𝓕 (hu.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) ξ := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hu.toLp u)
  let G : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hv.toLp v)
  let c : ℂ := 2 * Real.pi * Complex.I
  change (G : ℝ → ℂ) =ᵐ[volume] fun ξ : ℝ => c * (ξ : ℂ) * F ξ
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp G).locallyIntegrable (by norm_num))
    (LocallyIntegrable.continuous_mul (by fun_prop)
      ((Lp.memLp F).locallyIntegrable (by norm_num)))
  intro a ha hcompact
  have hac : HasCompactSupport (Complex.ofRealCLM ∘ a) := hcompact.comp_left rfl
  have has : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ a) := Complex.ofRealCLM.contDiff.comp ha
  let φ : 𝓢(ℝ, ℂ) := hac.toSchwartzMap has
  let η : 𝓢(ℝ, ℂ) := c • SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => ξ) φ
  have hηgrowth : (fun ξ : ℝ => ξ).HasTemperateGrowth := by fun_prop
  have hη (ξ : ℝ) : η ξ = c * (ξ : ℂ) * φ ξ := by
    simp [η, SchwartzMap.smulLeftCLM_apply_apply hηgrowth, Complex.real_smul,
      smul_eq_mul, mul_assoc]
  have hd : SchwartzMap.derivCLM ℂ ℂ (𝓕 φ) = -𝓕 η :=
    real_schwartz_deriv_fourier φ
  have hp : (∫ ξ : ℝ, φ ξ * G ξ) =
      ∫ ξ : ℝ, φ ξ * (c * (ξ : ℂ) * F ξ) := by
    calc
      _ = ∫ x : ℝ, (𝓕 φ) x * v x := real_l2_fourier_pairing v hv φ
      _ = - ∫ x : ℝ, SchwartzMap.derivCLM ℂ ℂ (𝓕 φ) x * u x :=
        real_l2_integral_mul_deriv u v hu hv hderiv (𝓕 φ)
      _ = ∫ x : ℝ, (𝓕 η) x * u x := by
        rw [hd]
        simp only [SchwartzMap.neg_apply, neg_mul, integral_neg, neg_neg]
      _ = ∫ ξ : ℝ, η ξ * F ξ := (real_l2_fourier_pairing u hu η).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ξ => by
          dsimp only
          rw [hη]
          ring
  simpa [φ, Complex.real_smul, smul_eq_mul] using hp

end ContinuousFlexibility.Analysis
