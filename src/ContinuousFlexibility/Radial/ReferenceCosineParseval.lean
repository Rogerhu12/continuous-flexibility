import ContinuousFlexibility.Radial.ReferenceCosineProjection
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Parseval identity in the even π-periodic cosine sector

The complex Fourier theorem is applied on one π-period. Reflection makes
its coefficients real. Pairing the positive and negative integer indices
then yields the exact normalized constant/even-cosine Parseval identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
open ContinuousFlexibility.Statements

private instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem radialAngularMean_eq_halfPeriod {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi)
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    radialAngularMean f = Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  have hleft : IntervalIntegrable f volume 0 Real.pi := hf.mono_set (by
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le (by positivity)]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
  have hright : IntervalIntegrable f volume Real.pi (2 * Real.pi) := hf.mono_set (by
    rw [uIcc_of_le (by linarith [Real.pi_pos]), uIcc_of_le (by positivity)]
    exact Icc_subset_Icc Real.pi_pos.le le_rfl)
  have hshift : (∫ θ in Real.pi..2 * Real.pi, f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    simpa only [zero_add, two_mul] using hp.intervalIntegral_add_eq Real.pi 0
  unfold radialAngularMean
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hshift]
  field_simp [Real.pi_ne_zero]
  <;> ring

private def halfPeriodFourierCoefficient (f : ℝ → ℝ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.pi_pos (fun θ => (f θ : ℂ)) n

private theorem halfPeriodFourierCoefficient_eq (f : ℝ → ℝ) (n : ℤ) :
    halfPeriodFourierCoefficient f n =
      ((Real.pi⁻¹ : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ) := by
  simp only [halfPeriodFourierCoefficient, fourierCoeffOn_eq_integral,
    fourier_coe_apply, sub_zero, one_div, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv]

private theorem halfPeriodFourierCoefficient_conj {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) (n : ℤ) :
    conj (halfPeriodFourierCoefficient f n) = halfPeriodFourierCoefficient f n := by
  let g (θ : ℝ) : ℂ := fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)
  have hreflect (θ : ℝ) : g (Real.pi - θ) = conj (g θ) := by
    have hf : f (Real.pi - θ) = f θ := by
      rw [sub_eq_add_neg, add_comm, hp, he]
    have hmode : fourier (-n) ((Real.pi - θ : ℝ) : AddCircle Real.pi) =
        conj (fourier (-n) (θ : AddCircle Real.pi)) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, fourier_apply,
        smul_neg, fourier_neg']
    simp only [g, hf, hmode, map_mul, Complex.conj_ofReal]
  have hi : conj (∫ θ in (0 : ℝ)..Real.pi, g θ) =
      ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    rw [← intervalIntegral.intervalIntegral_conj]
    calc
      (∫ θ in (0 : ℝ)..Real.pi, conj (g θ)) =
          ∫ θ in (0 : ℝ)..Real.pi, g (Real.pi - θ) :=
        intervalIntegral.integral_congr (fun θ _ => (hreflect θ).symm)
      _ = ∫ θ in (0 : ℝ)..Real.pi, g θ := by
        rw [intervalIntegral.integral_comp_sub_left]
        simp only [sub_self, sub_zero]
  rw [halfPeriodFourierCoefficient_eq, map_mul, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => ((Real.pi⁻¹ : ℝ) : ℂ) * z) hi

private theorem fourier_pi_re (n : ℤ) (θ : ℝ) :
    (fourier n (θ : AddCircle Real.pi)).re = Real.cos (2 * (n : ℝ) * θ) := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * n * θ / Real.pi =
        ((2 * (n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

private theorem halfPeriodFourierCoefficient_re {f : ℝ → ℝ}
    (hf : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 Real.pi) (n : ℤ) :
    (halfPeriodFourierCoefficient f n).re =
      Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.cos (2 * (n : ℝ) * θ) := by
  have hg : IntervalIntegrable
      (fun θ => fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)) volume 0 Real.pi :=
    hf.continuousOn_mul
      (((fourier (-n) : C(AddCircle Real.pi, ℂ)).continuous.comp
        (AddCircle.continuous_mk' Real.pi)).continuousOn)
  rw [halfPeriodFourierCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hre :
      (∫ θ in (0 : ℝ)..Real.pi,
        fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)).re =
      ∫ θ in (0 : ℝ)..Real.pi,
        (fourier (-n) (θ : AddCircle Real.pi) * (f θ : ℂ)).re :=
    (intervalIntegral.intervalIntegral_re hg).symm
  rw [hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    fourier_pi_re, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]
  ring

private theorem halfPeriodFourierCoefficient_norm_sq {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) (n : ℤ) :
    ‖halfPeriodFourierCoefficient f n‖ ^ 2 = (halfPeriodFourierCoefficient f n).re ^ 2 := by
  have him : (halfPeriodFourierCoefficient f n).im = 0 := by
    have h := congrArg Complex.im (halfPeriodFourierCoefficient_conj hp he n)
    simp only [Complex.conj_im] at h
    linarith
  have hreal : halfPeriodFourierCoefficient f n =
      ((halfPeriodFourierCoefficient f n).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_re]

private theorem periodic_cos_even_int (n : ℤ) :
    Function.Periodic (fun θ : ℝ => Real.cos (2 * (n : ℝ) * θ)) Real.pi := by
  intro θ
  convert Real.cos_add_int_mul_two_pi (2 * (n : ℝ) * θ) n using 1 <;> congr 1 <;> ring

/-- The normalized constant and positive even cosines give Parseval for
every actual even π-periodic L² angular section. -/
theorem hasSum_sq_referenceAngularCoefficient {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hp : Function.Periodic f Real.pi) (he : Function.Even f) :
    HasSum (fun n : ℕ => referenceAngularCoefficient f n ^ 2)
      (radialAngularMean (fun θ => f θ ^ 2)) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hhalf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi)) :=
    hf.mono_measure (Measure.restrict_mono_set _ (Ioc_subset_Ioc le_rfl
      (by linarith [Real.pi_pos])))
  have hhalfC : MemLp (fun θ => (f θ : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) Real.pi)) := hhalf.ofReal
  have hi : IntervalIntegrable f volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr
      (memLp_one_iff_integrable.mp (hf.mono_exponent (by norm_num)))
  have hiC : IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
      (memLp_one_iff_integrable.mp (hhalfC.mono_exponent (by norm_num)))
  have hisq : IntervalIntegrable (fun θ => f θ ^ 2) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr hf.integrable_sq
  have hParse : HasSum (fun n : ℤ => ‖halfPeriodFourierCoefficient f n‖ ^ 2)
      (radialAngularMean (fun θ => f θ ^ 2)) := by
    have h := hasSum_sq_fourierCoeffOn Real.pi_pos hhalfC
    have hpsq : Function.Periodic (fun θ => f θ ^ 2) Real.pi := by
      intro θ
      change f (θ + Real.pi) ^ 2 = f θ ^ 2
      rw [hp θ]
    rw [radialAngularMean_eq_halfPeriod hpsq hisq]
    simpa only [halfPeriodFourierCoefficient, sub_zero, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, smul_eq_mul] using h
  have hzero : referenceAngularCoefficient f 0 =
      (halfPeriodFourierCoefficient f 0).re := by
    rw [referenceAngularCoefficient_zero, radialAngularMean_eq_halfPeriod hp hi,
      halfPeriodFourierCoefficient_re hiC]
    simp only [Int.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  have hsucc (n : ℕ) : referenceAngularCoefficient f (n + 1) =
      Real.sqrt 2 * (halfPeriodFourierCoefficient f ((n + 1 : ℕ) : ℤ)).re := by
    rw [halfPeriodFourierCoefficient_re hiC]
    have hcos : IntervalIntegrable
        (fun θ => f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))
        volume 0 (2 * Real.pi) :=
      hi.mul_continuousOn
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hper : Function.Periodic
        (fun θ => f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ)) Real.pi := by
      simpa only [Function.Periodic, Pi.mul_apply, Int.cast_natCast] using
        hp.mul (periodic_cos_even_int ((n + 1 : ℕ) : ℤ))
    have hmean := radialAngularMean_eq_halfPeriod hper hcos
    have hscale : referenceAngularCoefficient f (n + 1) =
        Real.sqrt 2 * radialAngularMean
          (fun θ => f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ)) := by
      unfold referenceAngularCoefficient referenceAngularBasis cosineMode
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      have heq : (fun θ => f θ * (Real.sqrt 2 * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))) =
          (fun θ => Real.sqrt 2 * (f θ * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ))) := by
        funext θ
        ring
      rw [heq, radialAngularMean_const_mul]
    rw [hscale, hmean]
    simp only [Int.cast_natCast]
  have hneg (n : ℕ) : ‖halfPeriodFourierCoefficient f (-(n : ℤ))‖ ^ 2 =
      ‖halfPeriodFourierCoefficient f (n : ℤ)‖ ^ 2 := by
    rw [halfPeriodFourierCoefficient_norm_sq hp he,
      halfPeriodFourierCoefficient_norm_sq hp he,
      halfPeriodFourierCoefficient_re hiC, halfPeriodFourierCoefficient_re hiC]
    simp only [Int.cast_neg, mul_neg, neg_mul, Real.cos_neg]
  have hpaired := hParse.nat_add_neg
  have hatom := hasSum_ite_eq (0 : ℕ) (‖halfPeriodFourierCoefficient f 0‖ ^ 2)
  have hdiff := hpaired.sub hatom
  convert hdiff using 1
  · funext n
    rw [hneg]
    cases n with
    | zero =>
      simp only [Nat.cast_zero, ite_true, add_sub_cancel_right, hzero,
        halfPeriodFourierCoefficient_norm_sq hp he]
    | succ n =>
      simp only [Nat.succ_ne_zero, ite_false, sub_zero, hsucc,
        halfPeriodFourierCoefficient_norm_sq hp he, mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring
  · ring

end ContinuousFlexibility.Radial
