module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Fourier coefficients of actual smooth circle functions

This file obtains rapid coefficient summability from genuine smoothness and
periodicity.  The coefficients are mathlib's integral Fourier coefficients,
and the derivative identity is integration by parts on a full period.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff BigOperators

/-- The integral Fourier coefficient on a full period of length `2 * pi`. -/
def circleFourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n

theorem circleFourierCoeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    circleFourierCoeff f n = (1 / (2 * Real.pi)) •
      ∫ x in (0 : ℝ)..2 * Real.pi,
        fourier (-n) (x : AddCircle (2 * Real.pi)) • f x := by
  rw [circleFourierCoeff, fourierCoeffOn_eq_integral, sub_zero]

/-- Every ordinary derivative of a periodic function has the same period.
The translation identity also applies when a total derivative is zero. -/
theorem circlePeriodic_iteratedDeriv {f : ℝ → ℂ} {P : ℝ}
    (hp : Function.Periodic f P) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) P := by
  have heq : (fun x : ℝ => f (x + P)) = f := funext hp
  intro x
  have h := congrArg (fun g : ℝ → ℂ => iteratedDeriv k g x) heq
  simpa only [iteratedDeriv_comp_add_const] using h

/-- An integral coefficient is bounded by any uniform bound for the
function on its integration interval. -/
theorem norm_circleFourierCoeff_le {f : ℝ → ℂ} {B : ℝ}
    (hB : ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi), ‖f x‖ ≤ B) (n : ℤ) :
    ‖circleFourierCoeff f n‖ ≤ B := by
  have hP : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb : ‖∫ x in (0 : ℝ)..2 * Real.pi,
      fourier (-n) (x : AddCircle (2 * Real.pi)) • f x‖ ≤
      B * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact hB x (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hP.le] using hx))
  rw [circleFourierCoeff_eq_integral, norm_smul]
  calc
    ‖1 / (2 * Real.pi)‖ * ‖∫ x in (0 : ℝ)..2 * Real.pi,
        fourier (-n) (x : AddCircle (2 * Real.pi)) • f x‖ ≤
        ‖1 / (2 * Real.pi)‖ * (B * |2 * Real.pi - 0|) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = B := by
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hP), sub_zero, abs_of_pos hP]
      field_simp

/-- Integration by parts gives the exact gain of one frequency in norm. -/
theorem norm_circleFourierCoeff_deriv {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hd : Continuous (deriv f))
    (hp : Function.Periodic f (2 * Real.pi)) {n : ℤ} (hn : n ≠ 0) :
    ‖circleFourierCoeff (deriv f) n‖ =
      ‖circleFourierCoeff f n‖ * ‖(n : ℂ)‖ := by
  have hp0 : f (2 * Real.pi) = f 0 := by simpa only [zero_add] using hp 0
  have hi := fourierCoeffOn_of_hasDerivAt
    (by positivity : (0 : ℝ) < 2 * Real.pi) hn
    (fun x _ => (hf x).hasDerivAt) (hd.intervalIntegrable 0 (2 * Real.pi))
  have hformula : circleFourierCoeff f n =
      (1 / (-2 * (Real.pi : ℂ) * Complex.I * n)) *
        (-(2 * (Real.pi : ℂ)) * circleFourierCoeff (deriv f) n) := by
    simpa only [circleFourierCoeff, hp0, sub_self, mul_zero, zero_sub,
      sub_zero, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_zero, neg_mul] using hi
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnNorm : ‖(n : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hnC
  have heq : ‖circleFourierCoeff f n‖ =
      ‖circleFourierCoeff (deriv f) n‖ / ‖(n : ℂ)‖ := by
    rw [hformula]
    simp only [norm_mul, norm_div, norm_one, norm_neg, Complex.norm_I, mul_one]
    norm_num only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero, hnNorm] <;> ring
  exact ((eq_div_iff hnNorm).mp heq).symm

/-- Iterating the integration-by-parts identity on an actual smooth
periodic function. -/
theorem norm_circleFourierCoeff_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi))
    (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ‖circleFourierCoeff (iteratedDeriv k f) n‖ =
      ‖circleFourierCoeff f n‖ * ‖(n : ℂ)‖ ^ k := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, pow_zero, mul_one]
  | succ k ih =>
      have hd : Continuous (deriv (iteratedDeriv k f)) := by
        rw [← iteratedDeriv_succ]
        exact hf.continuous_iteratedDeriv (k + 1) (by simp)
      rw [iteratedDeriv_succ,
        norm_circleFourierCoeff_deriv
          (hf.differentiable_iteratedDeriv k
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)) hd
          (circlePeriodic_iteratedDeriv hp k) hn,
        ih, pow_succ, mul_assoc]

/-- At every order the integral Fourier coefficients have polynomial
decay.  The constant is obtained from the corresponding genuine derivative. -/
theorem circleFourierCoeff_moment_bound {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (s : ℕ) :
    ∃ B : ℝ, ∀ n : ℤ, n ≠ 0 →
      ‖circleFourierCoeff f n‖ * ‖(n : ℂ)‖ ^ s ≤ B / ‖(n : ℂ)‖ ^ 2 := by
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv (s + 2) (by simp)).continuousOn
  refine ⟨B, fun n hn => ?_⟩
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hnC) 2)).mpr
  rw [mul_assoc, ← pow_add, ← norm_circleFourierCoeff_iteratedDeriv hf hp (s + 2) hn]
  exact norm_circleFourierCoeff_le hB n

/-- Rapid absolute summability of the integral coefficients, on the full
integer frequency set.  The isolated zero mode is handled explicitly. -/
theorem summable_circleFourierCoeff_moment {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (s : ℕ) :
    Summable (fun n : ℤ => ‖circleFourierCoeff f n‖ * ‖(n : ℂ)‖ ^ s) := by
  obtain ⟨B, hB⟩ := circleFourierCoeff_moment_bound hf hp s
  have hseries : Summable (fun n : ℤ => 1 / ‖(n : ℂ)‖ ^ 2) := by
    apply Summable.of_nat_of_neg
    · simpa only [Int.cast_natCast, Complex.norm_natCast] using
        (Real.summable_one_div_nat_pow (p := 2)).mpr (by omega)
    · simpa only [Int.cast_neg, Int.cast_natCast, norm_neg, Complex.norm_natCast] using
        (Real.summable_one_div_nat_pow (p := 2)).mpr (by omega)
  have hzero : Summable (fun n : ℤ =>
      if n = 0 then ‖circleFourierCoeff f 0‖ else 0) :=
    (hasSum_ite_eq (0 : ℤ) ‖circleFourierCoeff f 0‖).summable
  apply Summable.of_nonneg_of_le
    (g := fun n : ℤ => ‖circleFourierCoeff f n‖ * ‖(n : ℂ)‖ ^ s)
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) s))
    (f := fun n : ℤ => B * (1 / ‖(n : ℂ)‖ ^ 2) +
      if n = 0 then ‖circleFourierCoeff f 0‖ else 0) ?_
    ((hseries.mul_left B).add hzero)
  intro n
  by_cases hn : n = 0
  · subst n
    cases s <;> simp
  · simpa only [hn, if_false, add_zero, mul_one_div] using hB n hn

/-- Smoothness alone supplies the absolute summability needed by mathlib's
pointwise Fourier reconstruction theorem. -/
theorem summable_circleFourierCoeff {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) :
    Summable (circleFourierCoeff f) := by
  apply Summable.of_norm
  simpa only [pow_zero, mul_one] using summable_circleFourierCoeff_moment hf hp 0

/-- The exponential monomial in physical angular coordinates. -/
theorem circleFourier_phase (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * Real.pi)) =
      Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast <;> field_simp <;> ring

/-- Pointwise reconstruction of a smooth periodic complex function from
its integral Fourier coefficients. -/
theorem hasSum_circleFourier {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (θ : ℝ) :
    HasSum (fun n : ℤ => circleFourierCoeff f n *
      Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)) (f θ) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    { toFun := hp.lift
      continuous_toFun := by
        apply (QuotientAddGroup.isQuotientMap_mk
          (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
        simpa only [Function.comp_def, Function.Periodic.lift_coe] using hf.continuous }
  have hF (x : ℝ) : F (x : AddCircle (2 * Real.pi)) = f x := hp.lift_coe x
  have hcoeff (n : ℤ) : fourierCoeff F n = circleFourierCoeff f n := by
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, circleFourierCoeff_eq_integral]
    simp only [zero_add, hF]
  have hsum : Summable (fourierCoeff F) :=
    (summable_circleFourierCoeff hf hp).congr (fun n => (hcoeff n).symm)
  simpa only [smul_eq_mul, hcoeff, hF, circleFourier_phase] using
    has_pointwise_sum_fourier_series_of_summable hsum (θ : AddCircle (2 * Real.pi))

/-- The zero Fourier coefficient vanishes when the actual integral does. -/
theorem circleFourierCoeff_zero_of_integral_eq_zero {f : ℝ → ℝ}
    (hm : ∫ x in (0 : ℝ)..2 * Real.pi, f x = 0) :
    circleFourierCoeff (fun x => (f x : ℂ)) 0 = 0 := by
  rw [circleFourierCoeff_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, intervalIntegral.integral_ofReal,
    hm, Complex.ofReal_zero, smul_zero]

/-- Averaging the actual Fourier reconstruction at opposite angles
removes the sine terms of an even function. -/
theorem hasSum_circleFourier_cosine_int {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi))
    (he : Function.Even f) (θ : ℝ) :
    HasSum (fun n : ℤ => (circleFourierCoeff (fun x => (f x : ℂ)) n).re *
      Real.cos ((n : ℝ) * θ)) (f θ) := by
  have hg : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hgp : Function.Periodic (fun x => (f x : ℂ)) (2 * Real.pi) :=
    fun x => congrArg Complex.ofReal (hp x)
  have hpos := hasSum_circleFourier hg hgp θ
  have hneg := hasSum_circleFourier hg hgp (-θ)
  have h := (Complex.hasSum_re (hpos.add hneg)).div_const 2
  convert h using 1
  · funext n
    simp only [mul_neg, Complex.add_re, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.cos_neg, Real.sin_neg]
    ring
  · simp only [Complex.add_re, Complex.ofReal_re, he θ]
    ring

/-- Pair the positive and negative integral Fourier coefficients.
For zero-mean functions the zero entry is zero. -/
def circleCosineCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)).re +
    (circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))).re

theorem circleCosineCoeff_zero {f : ℝ → ℝ}
    (hm : ∫ x in (0 : ℝ)..2 * Real.pi, f x = 0) : circleCosineCoeff f 0 = 0 := by
  simp only [circleCosineCoeff, Nat.cast_zero, neg_zero,
    circleFourierCoeff_zero_of_integral_eq_zero hm, Complex.zero_re, add_zero]

/-- The cosine coefficients obtained from the actual smooth function are
rapidly absolutely summable, with all integer moments. -/
theorem summable_circleCosineCoeff_moment {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi)) (s : ℕ) :
    Summable (fun j : ℕ => |circleCosineCoeff f j| * (j : ℝ) ^ s) := by
  have hg : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hgp : Function.Periodic (fun x => (f x : ℂ)) (2 * Real.pi) :=
    fun x => congrArg Complex.ofReal (hp x)
  have hsum := summable_circleFourierCoeff_moment hg hgp s
  have hpos : Summable (fun j : ℕ =>
      ‖circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)‖ * (j : ℝ) ^ s) := by
    simpa only [Function.comp_def, Int.cast_natCast, Complex.norm_natCast] using
      hsum.comp_injective (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℤ)))
  have hneg : Summable (fun j : ℕ =>
      ‖circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))‖ * (j : ℝ) ^ s) := by
    simpa only [Function.comp_def, Int.cast_neg, Int.cast_natCast, norm_neg,
      Complex.norm_natCast] using
      hsum.comp_injective (neg_injective.comp
        (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℤ))))
  apply Summable.of_nonneg_of_le
    (g := fun j : ℕ => |circleCosineCoeff f j| * (j : ℝ) ^ s)
    (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg j) s))
    (f := fun j : ℕ =>
      ‖circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)‖ * (j : ℝ) ^ s +
      ‖circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))‖ * (j : ℝ) ^ s) ?_
    (hpos.add hneg)
  intro j
  dsimp only [circleCosineCoeff]
  calc
    _ ≤ (|(circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)).re| +
          |(circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))).re|) * (j : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg (Nat.cast_nonneg j) s)
    _ ≤ (‖circleFourierCoeff (fun x => (f x : ℂ)) (j : ℤ)‖ +
          ‖circleFourierCoeff (fun x => (f x : ℂ)) (-(j : ℤ))‖) * (j : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right
        (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
        (pow_nonneg (Nat.cast_nonneg j) s)
    _ = _ := by ring

/-- A zero-mean smooth even periodic function equals its actual cosine
series at every angle, rather than only almost everywhere. -/
theorem hasSum_circleCosineCoeff {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi))
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..2 * Real.pi, f x = 0) (θ : ℝ) :
    HasSum (fun j : ℕ => circleCosineCoeff f j * Real.cos (j * θ)) (f θ) := by
  have h := (hasSum_circleFourier_cosine_int hf hp he θ).nat_add_neg
  have hzero := circleFourierCoeff_zero_of_integral_eq_zero hm
  convert h using 1
  · funext j
    simp only [circleCosineCoeff, Int.cast_natCast, Int.cast_neg, neg_mul, Real.cos_neg]
    ring
  · simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one, hzero,
      Complex.zero_re, add_zero]

/-- A complete rapid cosine expansion, with no expansion assumption. -/
theorem exists_rapid_circleCosine_expansion {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2 * Real.pi))
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..2 * Real.pi, f x = 0) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧
      (∀ s : ℕ, Summable (fun j : ℕ => |c j| * (j : ℝ) ^ s)) ∧
      ∀ θ : ℝ, f θ = ∑' j : ℕ, c j * Real.cos (j * θ) := by
  exact ⟨circleCosineCoeff f, circleCosineCoeff_zero hm,
    summable_circleCosineCoeff_moment hf hp,
    fun θ => (hasSum_circleCosineCoeff hf hp he hm θ).tsum_eq.symm⟩

/-- The integral over two periods is twice the integral over one. -/
theorem circle_integral_two_pi {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f Real.pi) :
    (∫ x in (0 : ℝ)..2 * Real.pi, f x) =
      2 * ∫ x in (0 : ℝ)..Real.pi, f x := by
  have hshift : (∫ x in Real.pi..2 * Real.pi, f x) =
      ∫ x in (0 : ℝ)..Real.pi, f x := by
    simpa only [zero_add, ← two_mul] using hp.intervalIntegral_add_eq Real.pi 0
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 Real.pi) (hf.intervalIntegrable Real.pi (2 * Real.pi)), hshift]
  ring

/-- Translation by pi multiplies the `j`th cosine by its parity sign. -/
theorem circleCosineMode_half_period (j : ℕ) (θ : ℝ) :
    Real.cos ((j : ℝ) * (θ + Real.pi)) =
      (-1 : ℝ) ^ j * Real.cos ((j : ℝ) * θ) := by
  rw [mul_add, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi,
    mul_zero, sub_zero]
  ring

/-- The canonical cosine coefficients after projection to period pi. -/
def circlePiCosineCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  if Even j then circleCosineCoeff f j else 0

/-- The actual pi-periodic circle functions have a rapid zero-mean cosine
expansion supported on the even positive frequencies required by the
return operator.  The half-period averaging is performed on convergent
series, so it does not presume Fourier uniqueness or an expansion. -/
theorem circlePiCosineCoeff_spec {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0) :
    circlePiCosineCoeff f 0 = 0 ∧
      (∀ s : ℕ, Summable (fun j : ℕ => |circlePiCosineCoeff f j| * (j : ℝ) ^ s)) ∧
      (∀ j : ℕ, circlePiCosineCoeff f j ≠ 0 → Even j) ∧
      ∀ θ : ℝ, f θ = ∑' j : ℕ, circlePiCosineCoeff f j * Real.cos (j * θ) := by
  have hp2 : Function.Periodic f (2 * Real.pi) := by
    intro θ
    calc
      f (θ + 2 * Real.pi) = f ((θ + Real.pi) + Real.pi) := by congr 1; ring
      _ = f (θ + Real.pi) := hp (θ + Real.pi)
      _ = f θ := hp θ
  have hm2 : ∫ x in (0 : ℝ)..2 * Real.pi, f x = 0 := by
    rw [circle_integral_two_pi hf.continuous hp, hm, mul_zero]
  dsimp only [circlePiCosineCoeff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [circleCosineCoeff_zero hm2, ite_self]
  · intro s
    apply Summable.of_nonneg_of_le
      (g := fun j : ℕ => |if Even j then circleCosineCoeff f j else 0| * (j : ℝ) ^ s)
      (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg j) s))
      (f := fun j : ℕ => |circleCosineCoeff f j| * (j : ℝ) ^ s) ?_
      (summable_circleCosineCoeff_moment hf hp2 s)
    intro j
    by_cases hj : Even j
    · simp only [hj, if_true, le_refl]
    · simp only [hj, if_false, abs_zero, zero_mul]
      positivity
  · intro j hj
    by_contra hodd
    exact hj (if_neg hodd)
  · intro θ
    have hs := ((hasSum_circleCosineCoeff hf hp2 he hm2 θ).add
      (hasSum_circleCosineCoeff hf hp2 he hm2 (θ + Real.pi))).div_const 2
    have hfiltered : HasSum
        (fun j : ℕ => (if Even j then circleCosineCoeff f j else 0) * Real.cos (j * θ))
        (f θ) := by
      convert hs using 1
      · funext j
        rw [circleCosineMode_half_period]
        by_cases hj : Even j
        · simp only [hj, if_true, hj.neg_one_pow, one_mul]
          ring
        · have ho : Odd j := Nat.not_even_iff_odd.mp hj
          simp only [hj, if_false, ho.neg_one_pow, zero_mul]
          ring
      · rw [hp θ]
        ring
    exact hfiltered.tsum_eq.symm

/-- A rapid cosine expansion of a smooth pi-periodic even zero-mean
function, with no coefficient or expansion assumption on the input. -/
theorem exists_rapid_circleCosine_expansion_pi {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ x in (0 : ℝ)..Real.pi, f x = 0) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧
      (∀ s : ℕ, Summable (fun j : ℕ => |c j| * (j : ℝ) ^ s)) ∧
      (∀ j : ℕ, c j ≠ 0 → Even j) ∧
      ∀ θ : ℝ, f θ = ∑' j : ℕ, c j * Real.cos (j * θ) :=
  ⟨circlePiCosineCoeff f, circlePiCosineCoeff_spec hf hp he hm⟩

end ContinuousFlexibility.Analysis
