module

public import ContinuousFlexibility.Analysis.OpticalTravelVariation

/-!
# A quantitative obstruction to a tiny normalized optical control

For the square-root integral, unit first variation forces the product of
the second variation and the size of the affine radicand variation to be
bounded below.  The proof is an elementary integrated cubic inequality.
It uses actual integrals and introduces no arithmetic or indexing premise.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

private theorem abs_cube_tangent (x c : ℝ) (hc : 0 ≤ c) :
    3 * c ^ 2 * x - 2 * c ^ 3 ≤ |x| ^ 3 := by
  have hpoly : 0 ≤ (|x| - c) ^ 2 * (|x| + 2 * c) :=
    mul_nonneg (sq_nonneg (|x| - c))
      (add_nonneg (abs_nonneg x) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc))
  have hlin := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr (le_abs_self x))
  nlinarith only [hpoly, hlin]

/-- The pointwise cubic relation between the first and second optical
variations, followed by the tangent inequality for the absolute cube. -/
theorem sqrtAffine_variation_pointwise {u y B c : ℝ}
    (hy : 0 < y) (hu : |u| ≤ B) (hc : 0 ≤ c) :
    3 * c ^ 2 * (u / (2 * y)) - 2 * c ^ 3 ≤
      (B / 2) * (u ^ 2 / (4 * y ^ 3)) := by
  have hcube : |u / (2 * y)| ^ 3 =
      (|u| / 2) * (u ^ 2 / (4 * y ^ 3)) := by
    rw [abs_div, abs_of_pos (mul_pos zero_lt_two hy), div_pow, ← sq_abs u]
    field_simp [hy.ne'] <;> ring
  calc
    _ ≤ |u / (2 * y)| ^ 3 := abs_cube_tangent _ _ hc
    _ = (|u| / 2) * (u ^ 2 / (4 * y ^ 3)) := hcube
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hu (by norm_num))
      (div_nonneg (sq_nonneg u) (by positivity))

/-- If the actual first variation of a square-root integral is one,
the second variation cannot be small together with the affine perturbation.
The interval and derivative bound appear explicitly in the conclusion. -/
theorem sqrtAffine_normalized_curvature_bound {a b B : ℝ} {q u : ℝ → ℝ}
    (hab : a < b) (hq : ContinuousOn q (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hqpos : ∀ r ∈ Icc a b, 0 < q r) (huB : ∀ r ∈ Icc a b, |u r| ≤ B)
    (hunit : (∫ r in a..b, u r / (2 * Real.sqrt (q r))) = 1) :
    2 ≤ (b - a) ^ 2 * B *
      ∫ r in a..b, u r ^ 2 / (4 * Real.sqrt (q r) ^ 3) := by
  let v (r : ℝ) := u r / (2 * Real.sqrt (q r))
  let d (r : ℝ) := u r ^ 2 / (4 * Real.sqrt (q r) ^ 3)
  let c : ℝ := (b - a)⁻¹
  have hc : 0 ≤ c := (inv_pos.mpr (sub_pos.mpr hab)).le
  have hsqrt := Real.continuous_sqrt.comp_continuousOn hq
  have hv : ContinuousOn v (Icc a b) :=
    hu.div (continuousOn_const.mul hsqrt)
      (fun r hr => (mul_pos zero_lt_two (Real.sqrt_pos.mpr (hqpos r hr))).ne')
  have hd : ContinuousOn d (Icc a b) :=
    (hu.pow 2).div (continuousOn_const.mul (hsqrt.pow 3))
      (fun r hr => (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr (hqpos r hr)) 3)).ne')
  have hvi : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab.le
  have hdi : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab.le
  have hineq : (∫ r in a..b, 3 * c ^ 2 * v r - 2 * c ^ 3) ≤
      ∫ r in a..b, (B / 2) * d r :=
    intervalIntegral.integral_mono_on hab.le
      ((hvi.const_mul _).sub intervalIntegrable_const) (hdi.const_mul _)
      (fun r hr => sqrtAffine_variation_pointwise (Real.sqrt_pos.mpr (hqpos r hr)) (huB r hr) hc)
  have hleft : (∫ r in a..b, 3 * c ^ 2 * v r - 2 * c ^ 3) = 1 / (b - a) ^ 2 := by
    rw [intervalIntegral.integral_sub (hvi.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hunit, intervalIntegral.integral_const, smul_eq_mul]
    dsimp only [c]
    field_simp [(sub_pos.mpr hab).ne'] <;> ring
  rw [hleft, intervalIntegral.integral_const_mul] at hineq
  have hmul := (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hab))).mp hineq
  change 1 ≤ ((B / 2) * ∫ r in a..b, d r) * (b - a) ^ 2 at hmul
  calc
    2 ≤ 2 * (((B / 2) * ∫ r in a..b, d r) * (b - a) ^ 2) := by linarith only [hmul]
    _ = _ := by dsimp only [d]; ring

/-- The same estimate records an upper bound for the actual second
variation as a real number, ready to combine with a tame flow estimate. -/
theorem sqrtAffine_normalized_control_lower_bound {a b B D : ℝ} {q u : ℝ → ℝ}
    (hab : a < b) (hq : ContinuousOn q (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hqpos : ∀ r ∈ Icc a b, 0 < q r) (huB : ∀ r ∈ Icc a b, |u r| ≤ B)
    (hunit : (∫ r in a..b, u r / (2 * Real.sqrt (q r))) = 1)
    (hD : (∫ r in a..b, u r ^ 2 / (4 * Real.sqrt (q r) ^ 3)) ≤ D) :
    2 ≤ (b - a) ^ 2 * B * D := by
  have hB : 0 ≤ B := (abs_nonneg (u a)).trans (huB a ⟨le_rfl, hab.le⟩)
  exact (sqrtAffine_normalized_curvature_bound hab hq hu hqpos huB hunit).trans
    (mul_le_mul_of_nonneg_left hD (mul_nonneg (sq_nonneg _) hB))

end ContinuousFlexibility.Analysis
