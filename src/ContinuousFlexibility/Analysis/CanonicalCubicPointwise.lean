module

public import ContinuousFlexibility.Analysis.CubicDivisionSmooth

/-!
# Pointwise cubic division with a fixed loss of three derivatives

The Taylor integral gives a bound at every derivative order, including the
removable endpoint.  The same constant `1 / 6` works for all orders, since
the additional factor `t ^ s` is at most one on the integration interval.

The hypotheses explicitly require the three vanishing boundary jets.  These
lemmas do not assert that a particular canonical coefficient has those jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Interval
open ContinuousFlexibility.Statements

private theorem cubicKernel_integral :
    (∫ t in (0 : ℝ)..1, (1 - t) ^ 2) = 1 / 3 := by
  calc
    (∫ t in (0 : ℝ)..1, (1 - t) ^ 2) = ∫ t in (0 : ℝ)..1, t ^ 2 := by
      simpa only [one_mul, inv_one, one_smul, sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_mul (fun t : ℝ => t ^ 2)
          (a := 0) (b := 1) (c := 1) one_ne_zero (1 : ℝ))
    _ = 1 / 3 := by norm_num

/-- A uniform bound for every moment of the positive cubic Taylor kernel.
The integrand need not itself be smooth; the conclusion uses only its bound. -/
theorem abs_cubicMoment_le_sixth {g : ℝ → ℝ} {M R y : ℝ}
    (hg : ∀ x ∈ Icc (0 : ℝ) R, |g x| ≤ M) (s : ℕ) (hy : y ∈ Icc (0 : ℝ) R) :
    |(1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * t ^ s * g (t * y)| ≤ M / 6 := by
  have hM : 0 ≤ M := (abs_nonneg (g 0)).trans (hg 0 ⟨le_rfl, hy.1.trans hy.2⟩)
  have hweight : IntervalIntegrable (fun t : ℝ => (1 - t) ^ 2 * M) volume 0 1 :=
    (((continuous_const.sub continuous_id).pow 2).mul continuous_const).intervalIntegrable 0 1
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖(1 - t) ^ 2 * t ^ s * g (t * y)‖ ≤ (1 - t) ^ 2 * M := by
    have hty : t * y ∈ Icc (0 : ℝ) R := by
      refine ⟨mul_nonneg ht.1.le hy.1, ?_⟩
      calc
        t * y ≤ 1 * y := mul_le_mul_of_nonneg_right ht.2 hy.1
        _ ≤ R := by simpa only [one_mul] using hy.2
    have hpow : t ^ s ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have hcoeff : 0 ≤ (1 - t) ^ 2 * t ^ s :=
      mul_nonneg (sq_nonneg _) (pow_nonneg ht.1.le _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff]
    calc
      (1 - t) ^ 2 * t ^ s * |g (t * y)| ≤ (1 - t) ^ 2 * t ^ s * M :=
        mul_le_mul_of_nonneg_left (hg _ hty) hcoeff
      _ ≤ ((1 - t) ^ 2 * 1) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)) hM
      _ = (1 - t) ^ 2 * M := by rw [mul_one]
  have hint := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall hpoint) hweight
  rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const, cubicKernel_integral] at hint
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * t ^ s * g (t * y)|
        ≤ (1 / 2 : ℝ) * ((1 / 3 : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hint (by norm_num)
    _ = M / 6 := by ring

/-- The exact derivative formula has three derivatives lost, independently
of the derivative order.  It holds on the whole real line. -/
theorem iteratedDeriv_cubicQuotient_eq_scaled_integral
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    (s : ℕ) (y : ℝ) :
    iteratedDeriv s (cubicQuotient f) y =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1,
        (1 - t) ^ 2 * t ^ s * iteratedDeriv (s + 3) f (t * y) := by
  have hf3 : ContDiff ℝ ∞ (iteratedDeriv 3 f) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv 3 hf
  have hw : Continuous (fun t : ℝ => (1 - t) ^ 2) :=
    (continuous_const.sub continuous_id).pow 2
  have hq : cubicQuotient f = fun y => (1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (t * y) :=
    funext (cubicQuotient_eq_integral hf hf0 hf1 hf2)
  rw [hq, iteratedDeriv_const_mul_field,
    iteratedDeriv_scaled_intervalIntegral hw hf3 s]
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- A pointwise `C^s` cubic-division estimate on any closed nonnegative interval.
Every order has the same constant, and the loss is exactly three derivatives. -/
theorem abs_iteratedDeriv_cubicQuotient_le_sixth
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    (s : ℕ) {M R y : ℝ}
    (hbound : ∀ x ∈ Icc (0 : ℝ) R, |iteratedDeriv (s + 3) f x| ≤ M)
    (hy : y ∈ Icc (0 : ℝ) R) :
    |iteratedDeriv s (cubicQuotient f) y| ≤ M / 6 := by
  rw [iteratedDeriv_cubicQuotient_eq_scaled_integral hf hf0 hf1 hf2]
  exact abs_cubicMoment_le_sixth hbound s hy

/-- In order zero, the regularized quotient is bounded by one sixth of the
uniform third-derivative bound, including at the removable singularity. -/
theorem abs_cubicQuotient_le_sixth
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (hf2 : iteratedDeriv 2 f 0 = 0)
    {M R y : ℝ} (hbound : ∀ x ∈ Icc (0 : ℝ) R, |iteratedDeriv 3 f x| ≤ M)
    (hy : y ∈ Icc (0 : ℝ) R) : |cubicQuotient f y| ≤ M / 6 := by
  simpa only [iteratedDeriv_zero, Nat.zero_add] using
    abs_iteratedDeriv_cubicQuotient_le_sixth hf hf0 hf1 hf2 0 hbound hy

end ContinuousFlexibility.Analysis
