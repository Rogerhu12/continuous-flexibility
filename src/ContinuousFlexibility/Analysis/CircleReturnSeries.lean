import ContinuousFlexibility.Analysis.CircleReturnAlgebra
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Infinite series for the circle return inverse

The finite-sum calculation for `M_T` extends to an actual smooth Fourier
series. A positive small-divisor margin costs one coefficient moment.
Every sum used below is proved summable; no identity relies on the default
value of a divergent `tsum`.

The input here is a rapidly summable sequence of cosine coefficients.
Identification of those coefficients for an arbitrary physical circle
function, and the weighted sequence-of-circles norm estimate, are separate
steps in the construction of `ReturnEquationData`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

/-- The infinite counterpart of the finite `circleReturnInverse`.
The frequency-zero summand is zero. -/
def circleReturnInverseSeries (c : ℕ → ℝ) (T θ : ℝ) : ℝ :=
  ∑' j : ℕ, c j / Real.sin (j * T) * Real.sin (j * θ)

theorem circleReturnInverseSeries_apply (c : ℕ → ℝ) (T θ : ℝ) :
    circleReturnInverseSeries c T θ =
      ∑' j : ℕ, c j / Real.sin (j * T) * Real.sin (j * θ) := rfl

/-- A summable absolute coefficient bound controls the sine series at
every angle, uniformly in that angle. -/
theorem summable_circleSineTerms {a : ℕ → ℝ}
    (ha : Summable (fun j => |a j|)) (θ : ℝ) :
    Summable (fun j : ℕ => a j * Real.sin (j * θ)) := by
  apply Summable.of_norm_bounded ha
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (j * θ)) (abs_nonneg (a j))

theorem summable_circleCosineTerms {a : ℕ → ℝ}
    (ha : Summable (fun j => |a j|)) (θ : ℝ) :
    Summable (fun j : ℕ => a j * Real.cos (j * θ)) := by
  apply Summable.of_norm_bounded ha
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (j * θ)) (abs_nonneg (a j))

/-- The coefficient estimate includes frequency zero, where the divided
coefficient is zero. The common constant is the reciprocal margin. -/
theorem circleReturn_divided_moment_le (c : ℕ → ℝ) {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|) (s j : ℕ) :
    |c j / Real.sin (j * T)| * (j : ℝ) ^ s ≤
      γ⁻¹ * (|c j| * (j : ℝ) ^ (s + 1)) := by
  by_cases hj : j = 0
  · subst j
    simp
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hb := circleReturn_coeff_bound c T γ j hγ hjpos (hT j hjpos)
    calc
      |c j / Real.sin (j * T)| * (j : ℝ) ^ s ≤
          ((j : ℝ) * |c j| / γ) * (j : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg (Nat.cast_nonneg j) s)
      _ = γ⁻¹ * (|c j| * (j : ℝ) ^ (s + 1)) := by
        rw [pow_succ]
        ring

/-- Division by the small divisor preserves rapid summability with a
loss of one moment. -/
theorem summable_circleReturn_divided_moment {c : ℕ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (s : ℕ) (hc : Summable (fun j : ℕ => |c j| * (j : ℝ) ^ (s + 1))) :
    Summable (fun j : ℕ => |c j / Real.sin (j * T)| * (j : ℝ) ^ s) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg j) s))
    (circleReturn_divided_moment_le c hγ hT s)
  exact hc.mul_left γ⁻¹

/-- Uniform bounds for every classical derivative of one sine term. -/
theorem circleSineTerm_iteratedFDeriv_bound (a : ℝ) (j s : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ s (fun x : ℝ => a * Real.sin (j * x)) θ‖ ≤
      |a| * (j : ℝ) ^ s := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (Real.contDiff_sin.of_le (by simp))]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg j) s)]
  calc
    |a| * ((j : ℝ) ^ s * |iteratedDeriv s Real.sin (j * θ)|) ≤
        |a| * ((j : ℝ) ^ s * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one s (j * θ))
          (pow_nonneg (Nat.cast_nonneg j) s)) (abs_nonneg a)
    _ = |a| * (j : ℝ) ^ s := by rw [mul_one]

/-- Rapidly summable sine coefficients define a genuine smooth function. -/
theorem contDiff_circleSineSeries {a : ℕ → ℝ}
    (ha : ∀ s : ℕ, Summable (fun j : ℕ => |a j| * (j : ℝ) ^ s)) :
    ContDiff ℝ ∞ (fun θ : ℝ => ∑' j : ℕ, a j * Real.sin (j * θ)) := by
  apply contDiff_tsum (N := ⊤)
    (v := fun s j => |a j| * (j : ℝ) ^ s)
  · intro j
    exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
  · intro s _
    exact ha s
  · intro s j θ _
    exact circleSineTerm_iteratedFDeriv_bound (a j) j s θ

/-- The inverse series is smooth at every order, with one common margin. -/
theorem contDiff_circleReturnInverseSeries {c : ℕ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hc : ∀ s : ℕ, Summable (fun j : ℕ => |c j| * (j : ℝ) ^ s)) :
    ContDiff ℝ ∞ (circleReturnInverseSeries c T) := by
  apply contDiff_circleSineSeries
  intro s
  exact summable_circleReturn_divided_moment hγ hT s (hc (s + 1))

theorem circleReturnInverseSeries_odd (c : ℕ → ℝ) (T θ : ℝ) :
    circleReturnInverseSeries c T (-θ) = -circleReturnInverseSeries c T θ := by
  rw [circleReturnInverseSeries_apply, circleReturnInverseSeries_apply, ← tsum_neg]
  apply tsum_congr
  intro j
  rw [mul_neg, Real.sin_neg, mul_neg]

/-- The return operator commutes with a convergent sine expansion. -/
theorem circleReturnShift_sineSeries {a : ℕ → ℝ}
    (ha : Summable (fun j => |a j|)) (T θ : ℝ) :
    circleReturnShift T (fun x : ℝ => ∑' j : ℕ, a j * Real.sin (j * x)) θ =
      ∑' j : ℕ, a j * Real.sin (j * T) * Real.cos (j * θ) := by
  have hp := summable_circleSineTerms ha (θ + T)
  have hm := summable_circleSineTerms ha (-θ + T)
  unfold circleReturnShift circleReturnEven
  rw [← hp.tsum_add hm, ← tsum_div_const]
  apply tsum_congr
  intro j
  simp only [mul_add, mul_neg, Real.sin_add, Real.sin_neg, Real.cos_neg]
  ring

/-- The exact infinite inverse identity, including the zero-frequency
compatibility. This is an identity of actual functions at every angle. -/
theorem circleReturnShift_inverseSeries {c : ℕ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hc : Summable (fun j : ℕ => |c j| * (j : ℝ))) (hc0 : c 0 = 0) (θ : ℝ) :
    circleReturnShift T (circleReturnInverseSeries c T) θ =
      ∑' j : ℕ, c j * Real.cos (j * θ) := by
  have ha : Summable (fun j => |c j / Real.sin (j * T)|) := by
    simpa only [pow_zero, mul_one, zero_add, pow_one] using
      summable_circleReturn_divided_moment hγ hT 0 (by simpa using hc)
  rw [show circleReturnInverseSeries c T =
    (fun x : ℝ => ∑' j : ℕ, c j / Real.sin (j * T) * Real.sin (j * x)) from rfl,
    circleReturnShift_sineSeries ha]
  apply tsum_congr
  intro j
  by_cases hj : j = 0
  · subst j
    simp [hc0]
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hjreal : (0 : ℝ) < j := by exact_mod_cast (Nat.pos_of_ne_zero hj)
    have hs : Real.sin (j * T) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (div_pos hγ hjreal) (hT j hjpos))
    rw [div_mul_cancel₀ _ hs]

/-- The same series has period pi when only even frequencies occur. -/
theorem circleReturnInverseSeries_periodic_pi {c : ℕ → ℝ}
    (hc : ∀ j : ℕ, c j ≠ 0 → Even j) (T : ℝ) :
    Function.Periodic (circleReturnInverseSeries c T) Real.pi := by
  intro θ
  rw [circleReturnInverseSeries_apply, circleReturnInverseSeries_apply]
  apply tsum_congr
  intro j
  by_cases hz : c j = 0
  · simp [hz]
  · obtain ⟨k, hk⟩ := hc j hz
    have hsin : Real.sin ((j : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi j
    have hcos : Real.cos ((j : ℝ) * Real.pi) = 1 := by
      rw [hk]
      have he : ((k + k : ℕ) : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
      rw [he, Real.cos_nat_mul_two_pi]
    rw [mul_add, Real.sin_add, hsin, hcos, mul_one, mul_zero, add_zero]

end ContinuousFlexibility.Analysis
