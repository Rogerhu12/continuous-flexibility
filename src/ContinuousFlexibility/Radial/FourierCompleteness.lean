import ContinuousFlexibility.Radial.AngularMeanL2
import ContinuousFlexibility.Radial.FourierSymmetry
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Completeness of the actual even half-turn cosine coefficients

The only completeness input is mathlib's Parseval identity on the ordinary
angular interval. The complex Fourier kernel is related explicitly to its
real cosine and sine parts. Symmetry then reduces all coefficients to the
mean and the positive even cosine moments of the raw L² function.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped BigOperators

theorem fourier_two_pi_neg_apply (n : ℤ) (θ : ℝ) :
    @fourier (2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) =
      (Real.cos ((n : ℝ) * θ) : ℂ) -
        (Real.sin ((n : ℝ) * θ) : ℂ) * Complex.I := by
  rw [fourier_coe_apply]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (θ : ℂ) /
          ((2 * Real.pi : ℝ) : ℂ) =
        ((-((n : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [hπ] <;> ring
  rw [hphase, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- Vanishing real moments give the corresponding actual complex Fourier coefficient. -/
set_option backward.isDefEq.respectTransparency false in
theorem angular_fourierCoeffOn_eq_zero_of_moments {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (n : ℤ)
    (hcos : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos ((n : ℝ) * θ)) = 0)
    (hsin : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.sin ((n : ℝ) * θ)) = 0) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi)
      (fun θ => (f θ : ℂ)) n = 0 := by
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hcLp : MemLp (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    angularInterval_memLp_of_continuous
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hsLp : MemLp (fun θ : ℝ => Real.sin ((n : ℝ) * θ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    angularInterval_memLp_of_continuous
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hc : IntervalIntegrable
      (fun θ : ℝ => ((f θ * Real.cos ((n : ℝ) * θ) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (Complex.ofRealCLM.integrable_comp (hf.integrable_mul hcLp))
  have hs : IntervalIntegrable
      (fun θ : ℝ => ((f θ * Real.sin ((n : ℝ) * θ) : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (Complex.ofRealCLM.integrable_comp (hf.integrable_mul hsLp))
  have hproduct (θ : ℝ) :
      @fourier (2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) * (f θ : ℂ) =
        ((f θ * Real.cos ((n : ℝ) * θ) : ℝ) : ℂ) -
          ((f θ * Real.sin ((n : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
    rw [fourier_two_pi_neg_apply]
    push_cast
    ring
  have hint :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        @fourier (2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) * (f θ : ℂ)) = 0 := by
    calc
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
          ((f θ * Real.cos ((n : ℝ) * θ) : ℝ) : ℂ) -
            ((f θ * Real.sin ((n : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact hproduct θ
      _ = (∫ θ in (0 : ℝ)..2 * Real.pi,
          ((f θ * Real.cos ((n : ℝ) * θ) : ℝ) : ℂ)) -
          (∫ θ in (0 : ℝ)..2 * Real.pi,
            ((f θ * Real.sin ((n : ℝ) * θ) : ℝ) : ℂ)) * Complex.I := by
        rw [intervalIntegral.integral_sub hc (hs.mul_const Complex.I),
          intervalIntegral.integral_mul_const]
      _ = 0 := by
        rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hcos, hsin]
        simp
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul]
  change (1 / (2 * Real.pi) : ℝ) •
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      @fourier (2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) * (f θ : ℂ)) = 0
  rw [hint]
  simp

/-- Parseval supplies completeness; no pointwise convergence of a Fourier sum is asserted. -/
theorem ae_eq_zero_of_angular_fourierCoeffOn_zero {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hcoeff : ∀ n : ℤ, fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] 0 := by
  have hab : (0 : ℝ) < 2 * Real.pi := by positivity
  have henergy : (2 * Real.pi)⁻¹ *
      (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f θ‖ ^ 2) = 0 := by
    have h := (tsum_sq_fourierCoeffOn hab hf).symm
    simpa [hcoeff, smul_eq_mul] using h
  have hint : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f θ‖ ^ 2) = 0 :=
    (mul_eq_zero.mp henergy).resolve_left (by positivity)
  have hsquare : Integrable (fun θ : ℝ => ‖f θ‖ ^ 2)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hset : (∫ θ, ‖f θ‖ ^ 2 ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) = 0 := by
    simpa only [intervalIntegral.integral_of_le hab.le] using hint
  have hae : (fun θ : ℝ => ‖f θ‖ ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg ‖f θ‖) hsquare).mp hset
  filter_upwards [hae] with θ hθ
  change ‖f θ‖ ^ 2 = 0 at hθ
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hθ)

/-- The mean and the positive even cosine moments determine every raw
even, π-periodic L² function up to a.e. equality on an angular period. -/
theorem even_periodic_ae_eq_zero_of_cosine_coefficients {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (heven : Function.Even f) (hperiodic : Function.Periodic f Real.pi)
    (hmean : angularAverage f = 0)
    (hcoeff : ∀ j : ℕ, 0 < j → Even j → angularPairing f (cosineMode j) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] 0 := by
  have hc : MemLp (fun θ => (f θ : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := hf.ofReal
  have hz : (fun θ => (f θ : ℂ)) =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] 0 := by
    apply ae_eq_zero_of_angular_fourierCoeffOn_zero hc
    intro n
    exact angular_fourierCoeffOn_eq_zero_of_moments hf n
      (integral_mul_cos_int_eq_zero_of_even_coefficients hperiodic hmean hcoeff n)
      (integral_mul_sin_int_eq_zero_of_even_periodic heven hperiodic n)
  filter_upwards [hz] with θ hθ
  change (f θ : ℂ) = 0 at hθ
  change f θ = 0
  exact Complex.ofReal_eq_zero.mp hθ

end

end ContinuousFlexibility.Radial
