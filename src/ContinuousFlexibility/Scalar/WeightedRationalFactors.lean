import ContinuousFlexibility.Scalar.WeightedCoefficientFormulas

/-!
# Explicit small factors in the weighted scalar formulas

The square-root and inverse factors in the actual finite-jet formulas are
smooth on their positive domains. The identities below expose a discriminant,
angular, profile, or normalized-Q defect in every difference from the reference
value. They can therefore be estimated with one weighted height factor.
-/

noncomputable section

namespace ContinuousFlexibility

/-- Rationalization at the reference square root, valid also at zero. -/
theorem sqrt_one_add_sub_one_eq_factor {d : ℝ} (hd : 0 ≤ 1 + d) :
    Real.sqrt (1 + d) - 1 = d / (Real.sqrt (1 + d) + 1) := by
  have hs : Real.sqrt (1 + d) + 1 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) zero_lt_one).ne'
  apply (eq_div_iff hs).2
  nlinarith [Real.sq_sqrt hd]

/-- Rationalization of two square roots with a positive denominator. -/
theorem sqrt_div_sqrt_sub_one_eq_factor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt a / Real.sqrt b - 1 =
      (a - b) / ((Real.sqrt a + Real.sqrt b) * Real.sqrt b) := by
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hsum : Real.sqrt a + Real.sqrt b ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hb)).ne'
  have hdiff : Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
    apply (eq_div_iff hsum).2
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le]
  calc
    Real.sqrt a / Real.sqrt b - 1 = (Real.sqrt a - Real.sqrt b) / Real.sqrt b := by
      field_simp [hsb]
      <;> ring
    _ = (a - b) / ((Real.sqrt a + Real.sqrt b) * Real.sqrt b) := by
      rw [hdiff, div_div]

/-- The coframe radial difference has an explicit first-order defect. -/
theorem sqrt_discriminant_div_angular_sub_one_eq_factor {d b : ℝ}
    (hd : 0 ≤ 1 + d) (hb : 0 < 1 - b ^ 2) :
    Real.sqrt (1 + d) / Real.sqrt (1 - b ^ 2) - 1 =
      (d + b ^ 2) /
        ((Real.sqrt (1 + d) + Real.sqrt (1 - b ^ 2)) * Real.sqrt (1 - b ^ 2)) := by
  rw [sqrt_div_sqrt_sub_one_eq_factor hd hb]
  congr 1
  ring

/-- The angular coframe difference is quadratic in its normalized angular jet. -/
theorem sqrt_one_sub_sq_sub_one_eq_factor {b : ℝ} (hb : 0 ≤ 1 - b ^ 2) :
    Real.sqrt (1 - b ^ 2) - 1 = -b ^ 2 / (Real.sqrt (1 - b ^ 2) + 1) := by
  have hd : 0 ≤ 1 + -(b ^ 2) := by simpa only [sub_eq_add_neg] using hb
  simpa only [sub_eq_add_neg] using
    (sqrt_one_add_sub_one_eq_factor (d := -(b ^ 2)) hd)

/-- The inverse-root difference contains a discriminant defect. -/
theorem inv_sqrt_one_add_sub_one_eq_factor {d : ℝ} (hd : 0 < 1 + d) :
    (Real.sqrt (1 + d))⁻¹ - 1 =
      -d / ((Real.sqrt (1 + d) + 1) * Real.sqrt (1 + d)) := by
  have hs : Real.sqrt (1 + d) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  calc
    (Real.sqrt (1 + d))⁻¹ - 1 =
        -(Real.sqrt (1 + d) - 1) / Real.sqrt (1 + d) := by
      field_simp [hs]
      <;> ring
    _ = -(d / (Real.sqrt (1 + d) + 1)) / Real.sqrt (1 + d) := by
      rw [sqrt_one_add_sub_one_eq_factor hd.le]
    _ = -d / ((Real.sqrt (1 + d) + 1) * Real.sqrt (1 + d)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The inverse three-halves factor has no constant part after subtraction. -/
theorem inverseDThreeHalves_one_add_sub_one_eq_factor {d : ℝ} (hd : 0 < 1 + d) :
    inverseDThreeHalves (1 + d) - 1 =
      -d * ((1 + d) + Real.sqrt (1 + d) + 1) /
        ((Real.sqrt (1 + d) + 1) * (1 + d) * Real.sqrt (1 + d)) := by
  let s := Real.sqrt (1 + d)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hsq : s ^ 2 = 1 + d := Real.sq_sqrt hd.le
  have hcube : (1 + d) * s - 1 = (s - 1) * ((1 + d) + s + 1) := by
    calc
      (1 + d) * s - 1 = (s - 1) * (s ^ 2 + s + 1) := by
        rw [← hsq]
        ring
      _ = (s - 1) * ((1 + d) + s + 1) := by rw [hsq]
  have hdiff : s - 1 = d / (s + 1) := sqrt_one_add_sub_one_eq_factor hd.le
  change 1 / ((1 + d) * s) - 1 =
    -d * ((1 + d) + s + 1) / ((s + 1) * (1 + d) * s)
  calc
    1 / ((1 + d) * s) - 1 = -((1 + d) * s - 1) / ((1 + d) * s) := by
      field_simp [hd.ne', hs]
      <;> ring
    _ = -((d / (s + 1)) * ((1 + d) + s + 1)) / ((1 + d) * s) := by
      rw [hcube, hdiff]
    _ = -d * ((1 + d) + s + 1) / ((s + 1) * (1 + d) * s) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The slope factor separates the normalized-Q and discriminant defects. -/
theorem normalizedSlopeFactor_sub_one_eq_factor {h d : ℝ}
    (hh : 1 + h ≠ 0) (hd : 0 < 1 + d) :
    (1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹ - 1 =
      -h / ((1 + h) * Real.sqrt (1 + d)) -
        d / ((Real.sqrt (1 + d) + 1) * Real.sqrt (1 + d)) := by
  have hinv : (1 + h)⁻¹ - 1 = -h / (1 + h) := by
    field_simp [hh]
    <;> ring
  calc
    (1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹ - 1 =
        ((1 + h)⁻¹ - 1) * (Real.sqrt (1 + d))⁻¹ +
          ((Real.sqrt (1 + d))⁻¹ - 1) := by ring
    _ = _ := by
      rw [hinv, inv_sqrt_one_add_sub_one_eq_factor hd]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- This is the normalized difference appearing in the actual radial
coefficient, with all reference-value subtraction already cancelled. -/
theorem normalizedRadialFactor_sub_one_eq_factor (m h : ℝ) {d : ℝ}
    (hd : 0 < 1 + d) :
    (1 + m) * (1 + h) * inverseDThreeHalves (1 + d) - 1 =
      (m + h + m * h) * inverseDThreeHalves (1 + d) -
        d * ((1 + d) + Real.sqrt (1 + d) + 1) /
          ((Real.sqrt (1 + d) + 1) * (1 + d) * Real.sqrt (1 + d)) := by
  calc
    (1 + m) * (1 + h) * inverseDThreeHalves (1 + d) - 1 =
        (m + h + m * h) * inverseDThreeHalves (1 + d) +
          (inverseDThreeHalves (1 + d) - 1) := by ring
    _ = _ := by rw [inverseDThreeHalves_one_add_sub_one_eq_factor hd]; ring

/-- This is the normalized difference multiplying the reference slope in
the actual corrected angular coefficient. -/
theorem normalizedProfileSlopeFactor_sub_one_eq_factor (m : ℝ) {h d : ℝ}
    (hh : 1 + h ≠ 0) (hd : 0 < 1 + d) :
    (1 + m) * ((1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹) - 1 =
      m * ((1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹) -
        h / ((1 + h) * Real.sqrt (1 + d)) -
        d / ((Real.sqrt (1 + d) + 1) * Real.sqrt (1 + d)) := by
  calc
    (1 + m) * ((1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹) - 1 =
        m * ((1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹) +
          ((1 + h)⁻¹ * (Real.sqrt (1 + d))⁻¹ - 1) := by ring
    _ = _ := by rw [normalizedSlopeFactor_sub_one_eq_factor hh hd]; ring

end ContinuousFlexibility
