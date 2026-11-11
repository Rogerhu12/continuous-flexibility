import ContinuousFlexibility.Analysis.RootCoefficientFactorization

/-!
# Actual positive value bounds used to recover the root speed

The numerical N01 intervals for Q/w and the discriminant bound the
actual radial coefficient. The divided determinant has the exact
reference-radicand formula. These identities provide the positive value
rectangle required by smooth composition, independently of higher jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem root_radial_coefficient_relative_bounds
    {w Q D : ℝ} (hw : 0 < w)
    (hQl : (7 / 8 : ℝ) ≤ Q / w) (hQu : Q / w ≤ (9 / 8 : ℝ))
    (hDl : (1 / 2 : ℝ) ≤ D) (hDu : D ≤ (3 / 2 : ℝ)) :
    w / 4 ≤ Q * inverseDThreeHalves D ∧
      Q * inverseDThreeHalves D ≤ 8 * w := by
  have hD : 0 < D := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hDl
  have hsq := Real.sq_sqrt hD.le
  have hsn := Real.sqrt_nonneg D
  have hsl : (1 / 2 : ℝ) ≤ Real.sqrt D := by nlinarith only [hsq, hDl, hsn]
  have hsu : Real.sqrt D ≤ 2 := by nlinarith only [hsq, hDu, hsn]
  have hden : 0 < D * Real.sqrt D := mul_pos hD (Real.sqrt_pos.mpr hD)
  have hdenl : (1 / 4 : ℝ) ≤ D * Real.sqrt D := by
    have hh := mul_le_mul hDl hsl (by norm_num : (0 : ℝ) ≤ 1 / 2) hD.le
    norm_num at hh ⊢
    exact hh
  have hdenu : D * Real.sqrt D ≤ 3 := by
    have hh := mul_le_mul hDu hsu hsn (by norm_num : (0 : ℝ) ≤ 3 / 2)
    norm_num at hh ⊢
    exact hh
  have hQl' : (7 / 8 : ℝ) * w ≤ Q := (le_div_iff₀ hw).mp hQl
  have hQu' : Q ≤ (9 / 8 : ℝ) * w := (div_le_iff₀ hw).mp hQu
  have hbounds : w / 4 ≤ Q / (D * Real.sqrt D) ∧
      Q / (D * Real.sqrt D) ≤ 8 * w := by
    constructor
    · apply (le_div_iff₀ hden).mpr
      have hm := mul_le_mul_of_nonneg_left hdenu hw.le
      nlinarith only [hm, hQl', hw]
    · apply (div_le_iff₀ hden).mpr
      have hm := mul_le_mul_of_nonneg_left hdenl hw.le
      nlinarith only [hm, hQu', hw]
  simpa only [inverseDThreeHalves, one_div, div_eq_mul_inv, one_mul] using hbounds

theorem root_positive_square_denominator_bounds
    {H D : ℝ} (hH : 0 ≤ H)
    (hDl : (1 / 2 : ℝ) ≤ D) (hDu : D ≤ (3 / 2 : ℝ)) :
    H / 4 ≤ H / D ^ 2 ∧ H / D ^ 2 ≤ 4 * H := by
  have hD : 0 < D := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hDl
  have hden : 0 < D ^ 2 := sq_pos_of_pos hD
  have hdenl : (1 / 4 : ℝ) ≤ D ^ 2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hD.le).mpr hDl
    norm_num at hh
    exact hh
  have hdenu : D ^ 2 ≤ 4 :=
    ((sq_le_sq₀ hD.le (by norm_num : (0 : ℝ) ≤ 3 / 2)).mpr hDu).trans (by norm_num)
  constructor
  · apply (le_div_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hdenu hH
    nlinarith only [hh]
  · apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hdenl hH
    nlinarith only [hh]

/-- The positive root speed is recovered from the actual divided
determinant and the actual radial coefficient, including at the root. -/
theorem factoredCharacteristicSpeed_eq_sqrt_div_coefficient
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ} {r σ : ℝ} {p : PolarPoint}
    (hr : 0 < (rootProfileShift r σ p).1)
    (hw : 0 < wref (rootProfileShift r σ p).1) (hg : 0 < g p.1)
    (hD : 0 < polarDiscriminant w z (rootProfileShift r σ p))
    (hQ : 0 < heightQ (profileEnergy w (rootProfileShift r σ p))
      (heightRadial z (rootProfileShift r σ p))
      (angularPartial (heightAngular z) (rootProfileShift r σ p))) :
    factoredCharacteristicSpeed wref g w z r σ p =
      Real.sqrt (rootCoefficientRadialFactor wref g w z r σ p) /
        polarLinearA w z (rootProfileShift r σ p) := by
  let a := polarLinearA w z (rootProfileShift r σ p)
  let c := factoredCharacteristicSpeed wref g w z r σ p
  have ha : 0 < a := mul_pos hQ (inverseDThreeHalves_pos _ hD)
  have hc : 0 < c := factoredCharacteristicSpeed_pos hr hw hg hD hQ
  change c = Real.sqrt (a ^ 2 * c ^ 2) / a
  rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos ha hc)]
  exact (eq_div_iff ha.ne').mpr (mul_comm c a)

end ContinuousFlexibility.Analysis
