module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Algebra.Order.Round
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Characteristic small divisor of the central model

Section 4, immediately after `eq:rad-eq-sc6b`, uses the angle
`T = π/(2√2)`. This file proves an actual sine lower bound for every
positive integer frequency, separately from any spectral gap assertion.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Real

def centralTravelAngle : ℝ := Real.pi / (2 * Real.sqrt 2)

theorem centralTravelAngle_eq :
    centralTravelAngle = Real.pi * Real.sqrt 2 / 4 := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold centralTravelAngle
  apply (div_eq_iff (mul_ne_zero (by norm_num) hs)).2
  calc
    _ = Real.pi * (Real.sqrt 2 ^ 2 / 2) := by rw [hs2]; ring
    _ = _ := by ring

/-- The integer norm cannot vanish at a positive frequency. -/
theorem central_integer_norm_ne_zero {k : ℕ} (hk : 0 < k) (m : ℤ) :
    (k : ℤ) ^ 2 - 8 * m ^ 2 ≠ 0 := by
  intro hn
  have hr : (k : ℝ) ^ 2 = 8 * (m : ℝ) ^ 2 := by
    exact_mod_cast (sub_eq_zero.mp hn)
  by_cases hm : m = 0
  · subst m
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hr
    nlinarith [sq_pos_of_pos hk']
  · have him : Irrational (((2 * m : ℤ) : ℝ) * Real.sqrt 2) :=
      irrational_sqrt_two.intCast_mul (mul_ne_zero (by norm_num) hm)
    have hsquare : (k : ℝ) ^ 2 = (((2 * m : ℤ) : ℝ) * Real.sqrt 2) ^ 2 := by
      calc
        _ = 8 * (m : ℝ) ^ 2 := hr
        _ = _ := by
          push_cast
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
    · exact him.ne_nat k h.symm
    · exact him.neg.ne_nat k h.symm

/-- Factoring the nonzero integer norm gives a quantitative distance from
any integer within half a unit of the central irrational phase. -/
theorem central_phase_distance_lower_bound {k : ℕ} (hk : 1 ≤ k) (m : ℤ)
    (hm : |(k : ℝ) * Real.sqrt 2 / 4 - (m : ℝ)| ≤ 1 / 2) :
    1 / (16 * (k : ℝ)) ≤ |(k : ℝ) * Real.sqrt 2 / 4 - (m : ℝ)| := by
  let y : ℝ := (k : ℝ) * Real.sqrt 2 / 4
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0 : ℝ) ≤ k := by positivity
  have hs₀ : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs₂ : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsbound : Real.sqrt 2 ≤ 2 := by nlinarith
  have hy₀ : 0 ≤ y := by dsimp [y]; positivity
  have hybound : y ≤ (k : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left hsbound hk₀
    dsimp [y]
    nlinarith
  have hy₂ : 8 * y ^ 2 = (k : ℝ) ^ 2 := by
    dsimp [y]
    rw [div_pow, mul_pow, hs₂]
    ring
  have hnorm : (1 : ℝ) ≤ |(k : ℝ) ^ 2 - 8 * (m : ℝ) ^ 2| := by
    exact_mod_cast Int.one_le_abs (central_integer_norm_ne_zero (Nat.succ_le_iff.mp hk) m)
  have hfactor : (k : ℝ) ^ 2 - 8 * (m : ℝ) ^ 2 =
      8 * (y - (m : ℝ)) * (y + (m : ℝ)) := by nlinarith [hy₂]
  have hconjugate : |y + (m : ℝ)| ≤ 2 * (k : ℝ) := by
    calc
      _ = |2 * y - (y - (m : ℝ))| := by congr 1; ring
      _ ≤ |2 * y| + |y - (m : ℝ)| := abs_sub _ _
      _ ≤ 2 * (k : ℝ) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * y)]
        change |y - (m : ℝ)| ≤ 1 / 2 at hm
        linarith
  rw [hfactor, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hnorm
  have hprod : 1 ≤ 16 * (k : ℝ) * |y - (m : ℝ)| := by
    have h := mul_le_mul_of_nonneg_left hconjugate
      (by positivity : 0 ≤ 8 * |y - (m : ℝ)|)
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ))).2
  change 1 ≤ |y - (m : ℝ)| * (16 * (k : ℝ))
  nlinarith [hprod]

/-- Jordan's inequality after reduction by the nearest integer multiple of π. -/
theorem twice_distance_round_le_abs_sin_pi (y : ℝ) :
    2 * |y - (round y : ℝ)| ≤ |Real.sin (Real.pi * y)| := by
  let m : ℤ := round y
  change 2 * |y - (m : ℝ)| ≤ |Real.sin (Real.pi * y)|
  have hm : |y - (m : ℝ)| ≤ 1 / 2 := abs_sub_round y
  have harg : |Real.pi * (y - (m : ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left hm Real.pi_pos.le]
  have hsin : |Real.sin (Real.pi * (y - (m : ℝ)))| =
      |Real.sin (Real.pi * y)| := by
    rw [show Real.pi * (y - (m : ℝ)) = Real.pi * y - (m : ℝ) * Real.pi by ring,
      Real.sin_sub_int_mul_pi]
    simp only [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  calc
    _ = (2 / Real.pi) * |Real.pi * (y - (m : ℝ))| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_ne_zero]
    _ ≤ |Real.sin (Real.pi * (y - (m : ℝ)))| := Real.mul_abs_le_abs_sin harg
    _ = _ := hsin

/-- The actual central characteristic small divisor, with explicit constant. -/
theorem central_sine_small_divisor (k : ℕ) (hk : 1 ≤ k) :
    (1 / 8 : ℝ) / (k : ℝ) ≤ |Real.sin ((k : ℝ) * centralTravelAngle)| := by
  let y : ℝ := (k : ℝ) * Real.sqrt 2 / 4
  have hd := central_phase_distance_lower_bound hk (round y) (abs_sub_round y)
  have hsin := twice_distance_round_le_abs_sin_pi y
  have hphase : (k : ℝ) * centralTravelAngle = Real.pi * y := by
    rw [centralTravelAngle_eq]
    dsimp [y]
    ring
  rw [hphase]
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (Nat.succ_le_iff.mp hk)
  have hscale : (1 / 8 : ℝ) / (k : ℝ) = 2 * (1 / (16 * (k : ℝ))) := by
    field_simp [hk₀.ne']
    ring
  rw [hscale]
  linarith

theorem exists_central_sine_small_divisor :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      c / (k : ℝ) ≤ |Real.sin ((k : ℝ) * centralTravelAngle)| :=
  ⟨1 / 8, by norm_num, central_sine_small_divisor⟩

end

end ContinuousFlexibility.Radial
