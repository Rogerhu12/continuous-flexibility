import ContinuousFlexibility.Radial.ReferenceCosineFourier
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Parseval in the real cosine sector

This file identifies the genuine circle Fourier coefficients with the
normalized physical cosine coefficients, and pairs the positive and
negative integer frequencies in Parseval.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem referencePiFourier_re (n : ℤ) (θ : ℝ) :
    (fourier n (θ : AddCircle Real.pi)).re =
      Real.cos (2 * (n : ℝ) * θ) := by
  rw [fourier_coe_apply]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ) / (Real.pi : ℂ) =
      ((2 * (n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [hπ] <;> ring
  rw [harg, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

theorem referencePiFourierCoeff_re {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) (n : ℤ) :
    (referencePiFourierCoeff f n).re =
      Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.cos (2 * (n : ℝ) * θ) := by
  have hc : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).2
    change Integrable (fun θ => (f θ : ℂ)) (volume.restrict (Ioc (0 : ℝ) Real.pi))
    exact MemLp.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hf.ofReal
  have hg : IntervalIntegrable
      (fun θ => fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ))
      volume 0 Real.pi :=
    hc.continuousOn_mul
      (((fourier (-n)).continuous.comp
        (AddCircle.continuous_mk' Real.pi)).continuousOn)
  unfold referencePiFourierCoeff
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, Complex.real_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have hre :
      (∫ θ in (0 : ℝ)..Real.pi,
        fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)).re =
      ∫ θ in (0 : ℝ)..Real.pi,
        (fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)).re := by
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.intervalIntegral_comp_comm hg).symm
  rw [hre]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with θ
  intro hθ
  change (fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)).re =
    f θ * Real.cos (2 * (n : ℝ) * θ)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, referencePiFourier_re, Int.cast_neg, mul_neg,
    neg_mul, Real.cos_neg]
  ring

theorem referencePiFourierCoeff_zero_re {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) :
    (referencePiFourierCoeff f 0).re = radialAngularMean f := by
  have hi : IntervalIntegrable f volume 0 Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).2
    change Integrable f (volume.restrict (Ioc (0 : ℝ) Real.pi))
    exact MemLp.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hf
  rw [referencePiFourierCoeff_re hf 0]
  simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  exact (radialAngularMean_eq_pi_mean hp hi).symm

/-- The `sqrt 2` in the frozen cosine mode is exactly the factor between
the real Fourier coefficient and the normalized cosine coefficient. -/
theorem referenceCosineCoeff_eq_sqrt_two_mul_piFourier_re {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) (n : ℕ) :
    radialAngularMean (fun θ => f θ * Radial.cosineMode (2 * n) θ) =
      Real.sqrt 2 * (referencePiFourierCoeff f (n : ℤ)).re := by
  have hi : IntervalIntegrable f volume 0 Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).2
    change Integrable f (volume.restrict (Ioc (0 : ℝ) Real.pi))
    exact MemLp.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hf
  have hc : Continuous (Radial.cosineMode (2 * n)) := by
    unfold Radial.cosineMode
    fun_prop
  have hip : IntervalIntegrable
      (fun θ => f θ * Radial.cosineMode (2 * n) θ) volume 0 Real.pi :=
    hi.mul_continuousOn hc.continuousOn
  have hper : Function.Periodic
      (fun θ => f θ * Radial.cosineMode (2 * n) θ) Real.pi := by
    intro θ
    change f (θ + Real.pi) * Radial.cosineMode (2 * n) (θ + Real.pi) =
      f θ * Radial.cosineMode (2 * n) θ
    rw [hp θ, Radial.cosineMode_even_frequency_periodic n θ]
  rw [radialAngularMean_eq_pi_mean hper hip, referencePiFourierCoeff_re hf]
  simp only [Int.cast_natCast]
  have heq : (fun θ => f θ * Radial.cosineMode (2 * n) θ) =
      fun θ => Real.sqrt 2 * (f θ * Real.cos (2 * (n : ℝ) * θ)) := by
    funext θ
    unfold Radial.cosineMode
    push_cast
    ring
  rw [heq, intervalIntegral.integral_const_mul]
  ring

theorem referencePiFourierCoeff_norm_sq {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ) (n : ℤ) :
    ‖referencePiFourierCoeff f n‖ ^ 2 = (referencePiFourierCoeff f n).re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    referencePiFourierCoeff_im_eq_zero hp he n]
  ring

theorem two_mul_referencePiFourierCoeff_norm_sq {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) (n : ℕ) :
    2 * ‖referencePiFourierCoeff f (n : ℤ)‖ ^ 2 =
      (radialAngularMean (fun θ => f θ * Radial.cosineMode (2 * n) θ)) ^ 2 := by
  rw [referenceCosineCoeff_eq_sqrt_two_mul_piFourier_re hp hf n,
    referencePiFourierCoeff_norm_sq hp he (n : ℤ), mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem summable_sq_referenceCosineCoeff {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) :
    Summable (fun n : ℕ =>
      (radialAngularMean (fun θ => f θ * Radial.cosineMode (2 * (n + 1)) θ)) ^ 2) := by
  have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    intro i j hij
    exact Nat.add_right_cancel (Int.ofNat_injective hij)
  have hs := (hasSum_sq_referencePiFourierCoeff hp hf).summable.comp_injective hinj
  refine (Summable.mul_left 2 hs).congr ?_
  intro n
  exact two_mul_referencePiFourierCoeff_norm_sq hp he hf (n + 1)

/-- Parseval for the exact real cosine modes in the even, pi-periodic sector.
The zero mode is the angular mean; positive modes have physical frequencies
`2, 4, 6, ...`. -/
theorem reference_cosine_parseval {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : ∀ θ, f (-θ) = f θ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi))) :
    radialAngularMean (fun θ => f θ ^ 2) =
      (radialAngularMean f) ^ 2 +
        ∑' n : ℕ,
          (radialAngularMean (fun θ => f θ * Radial.cosineMode (2 * (n + 1)) θ)) ^ 2 := by
  have hs := hasSum_sq_referencePiFourierCoeff hp hf
  have heven : Function.Even (fun n : ℤ => ‖referencePiFourierCoeff f n‖ ^ 2) := by
    intro n
    change ‖referencePiFourierCoeff f (-n)‖ ^ 2 = ‖referencePiFourierCoeff f n‖ ^ 2
    rw [referencePiFourierCoeff_neg hp he n]
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs.summable
  have hpNat :
      (∑' n : ℕ+, ‖referencePiFourierCoeff f (n : ℤ)‖ ^ 2) =
      ∑' n : ℕ, ‖referencePiFourierCoeff f ((n + 1 : ℕ) : ℤ)‖ ^ 2 :=
    tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => ‖referencePiFourierCoeff f (n : ℤ)‖ ^ 2)
  calc
    _ = ∑' n : ℤ, ‖referencePiFourierCoeff f n‖ ^ 2 := hs.tsum_eq.symm
    _ = ‖referencePiFourierCoeff f 0‖ ^ 2 +
        2 * ∑' n : ℕ+, ‖referencePiFourierCoeff f (n : ℤ)‖ ^ 2 := by
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hsplit
    _ = _ := by
      rw [referencePiFourierCoeff_norm_sq hp he 0,
        referencePiFourierCoeff_zero_re hp hf, hpNat, ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro n
      exact two_mul_referencePiFourierCoeff_norm_sq hp he hf (n + 1)

end ContinuousFlexibility.Statements
