import ContinuousFlexibility.Analysis.OneHighCircleFourierBasic

/-!
# Subadditivity of the physical circle frequency weight

These numerical inequalities transfer an output Sobolev weight onto one
input factor in the actual convolution formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

theorem circlePhysicalFrequency_add (P : ℝ) (m n : ℤ) :
    circlePhysicalFrequency P (m + n) =
      circlePhysicalFrequency P m + circlePhysicalFrequency P n := by
  simp only [circlePhysicalFrequency, Int.cast_add, mul_add]

theorem circleFrequencyWeight_sq (P : ℝ) (n : ℤ) :
    circleFrequencyWeight P n ^ 2 = 1 + circlePhysicalFrequency P n ^ 2 := by
  rw [circleFrequencyWeight, Real.sq_sqrt (by positivity)]

/-- The Bessel weight is subadditive on physical circle frequencies. -/
theorem circleFrequencyWeight_add_le (P : ℝ) (m n : ℤ) :
    circleFrequencyWeight P (m + n) ≤
      circleFrequencyWeight P m + circleFrequencyWeight P n := by
  have habs (j : ℤ) : |circlePhysicalFrequency P j| ≤ circleFrequencyWeight P j := by
    rw [circleFrequencyWeight, ← Real.sqrt_sq_eq_abs (circlePhysicalFrequency P j)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hprod : circlePhysicalFrequency P m * circlePhysicalFrequency P n ≤
      circleFrequencyWeight P m * circleFrequencyWeight P n :=
    (le_abs_self _).trans <| (abs_mul _ _).le.trans <|
      mul_le_mul (habs m) (habs n) (abs_nonneg _) (circleFrequencyWeight_pos P m).le
  apply (sq_le_sq₀ (circleFrequencyWeight_pos P (m + n)).le
    (add_nonneg (circleFrequencyWeight_pos P m).le
      (circleFrequencyWeight_pos P n).le)).mp
  have hm := circleFrequencyWeight_sq P m
  have hn := circleFrequencyWeight_sq P n
  have hmn := circleFrequencyWeight_sq P (m + n)
  rw [circlePhysicalFrequency_add] at hmn
  nlinarith [hprod]

/-- An output Sobolev weight can be placed on either one of two inputs.
The explicit constant is harmless for every natural order, including zero. -/
theorem circleFrequencyWeight_add_pow_le (P : ℝ) (m n : ℤ) (s : ℕ) :
    circleFrequencyWeight P (m + n) ^ s ≤
      (2 : ℝ) ^ s * (circleFrequencyWeight P m ^ s + circleFrequencyWeight P n ^ s) := by
  have hbase : circleFrequencyWeight P (m + n) ≤
      2 * max (circleFrequencyWeight P m) (circleFrequencyWeight P n) :=
    (circleFrequencyWeight_add_le P m n).trans (by
      linarith [le_max_left (circleFrequencyWeight P m) (circleFrequencyWeight P n),
        le_max_right (circleFrequencyWeight P m) (circleFrequencyWeight P n)])
  have hp := pow_le_pow_left₀ (circleFrequencyWeight_pos P (m + n)).le hbase s
  rw [mul_pow] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total (circleFrequencyWeight P m) (circleFrequencyWeight P n) with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (pow_nonneg (circleFrequencyWeight_pos P m).le s)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (pow_nonneg (circleFrequencyWeight_pos P n).le s)

/-- The same input/output weight inequality for extended nonnegative
Fourier majorants. -/
theorem circleFrequencyWeight_add_pow_ennreal_le (P : ℝ) (m n : ℤ) (s : ℕ) :
    ENNReal.ofReal (circleFrequencyWeight P (m + n)) ^ s ≤
      (2 : ℝ≥0∞) ^ s * (ENNReal.ofReal (circleFrequencyWeight P m) ^ s +
        ENNReal.ofReal (circleFrequencyWeight P n) ^ s) := by
  have h := ENNReal.ofReal_le_ofReal (circleFrequencyWeight_add_pow_le P m n s)
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  simpa only [ENNReal.ofReal_pow (circleFrequencyWeight_pos P (m + n)).le,
    ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), htwo,
    ENNReal.ofReal_add (pow_nonneg (circleFrequencyWeight_pos P m).le s)
      (pow_nonneg (circleFrequencyWeight_pos P n).le s),
    ENNReal.ofReal_pow (circleFrequencyWeight_pos P m).le,
    ENNReal.ofReal_pow (circleFrequencyWeight_pos P n).le] using h

end ContinuousFlexibility.Analysis
