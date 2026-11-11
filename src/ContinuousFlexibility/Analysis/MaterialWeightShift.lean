import ContinuousFlexibility.Analysis.MaterialMScale

/-!
# Material height weights under bounded coordinate changes

A bounded change of the nonnegative endpoint coordinate preserves the
exact power of the height weight. The resulting quadratic exponential
is absorbed by a fixed power of the actual material weight `E0`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

theorem rpow_le_mul_rpow_of_twoSided
    {f g K : ℝ} (hf : 0 < f) (hg : 0 < g) (hK : 0 < K)
    (hfg : f ≤ K * g) (hgf : g ≤ K * f) (γ : ℝ) :
    f ^ γ ≤ K ^ |γ| * g ^ γ := by
  by_cases hγ : 0 ≤ γ
  · have h := Real.rpow_le_rpow hf.le hfg hγ
    simpa only [Real.mul_rpow hK.le hg.le, abs_of_nonneg hγ] using h
  · have hγ' : γ ≤ 0 := le_of_not_ge hγ
    have hgf' : g / K ≤ f := (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hgf)
    have h := Real.rpow_le_rpow_of_nonpos (div_pos hg hK) hgf' hγ'
    rw [Real.div_rpow hg.le hK.le, div_eq_mul_inv, ← Real.rpow_neg hK.le] at h
    simpa only [abs_of_nonpos hγ', mul_comm] using h

theorem one_add_sq_le_materialE0Exponent {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ 2 ≤ 4 * materialE0Exponent y := by
  have hlog : 1 ≤ materialLogFactor y := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + y by linarith only [hy])
    simpa only [materialLogFactor, Real.log_exp] using h
  have hp : 0 ≤ y ^ (5 / 2 : ℝ) := Real.rpow_nonneg hy _
  have hsq : y ^ 2 ≤ 1 + y ^ (5 / 2 : ℝ) := by
    by_cases hy1 : y ≤ 1
    · have hh : y ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy1 2
      nlinarith only [hh, hp]
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy1)
        (by norm_num : (2 : ℝ) ≤ 5 / 2)
      rw [Real.rpow_two] at hh
      linarith only [hh]
  have hterm := mul_le_mul_of_nonneg_left hlog hp
  dsimp only [materialE0Exponent]
  nlinarith only [hsq, hterm, hp, sq_nonneg (y - 1)]

theorem cube_difference_le_materialE0Exponent
    {L x y : ℝ} (hL : 0 ≤ L) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : |x - y| ≤ L) :
    |x ^ 3 - y ^ 3| ≤ 12 * L * (1 + L) ^ 2 * materialE0Exponent y := by
  have hxL : x ≤ y + L := by linarith only [(abs_le.mp hxy).2]
  have hyL : y ≤ y + L := le_add_of_nonneg_right hL
  have hmax : max |x| |y| ≤ (1 + L) * (1 + y) := by
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    apply max_le
    · nlinarith only [hxL, hL, mul_nonneg hL hy]
    · nlinarith only [hyL, hL, mul_nonneg hL hy]
  have hp := pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg x)) hmax 2
  have habs : |x ^ 3 - y ^ 3| ≤ |x - y| * 3 * max |x| |y| ^ 2 := by
    simpa using (abs_pow_sub_pow_le x y 3)
  calc
    _ ≤ |x - y| * 3 * max |x| |y| ^ 2 := habs
    _ ≤ L * 3 * ((1 + L) * (1 + y)) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hxy (by norm_num)) hp
        (sq_nonneg _) (mul_nonneg hL (by norm_num))
    _ = (3 * L * (1 + L) ^ 2) * (1 + y) ^ 2 := by ring
    _ ≤ (3 * L * (1 + L) ^ 2) * (4 * materialE0Exponent y) :=
      mul_le_mul_of_nonneg_left (one_add_sq_le_materialE0Exponent hy)
        (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg _))
    _ = _ := by ring

/-- The exponent of `H` is unchanged; all loss lies in a fixed `E0` power. -/
theorem materialH_rpow_bounded_shift
    (γ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |x - y| ≤ L →
      materialH x ^ γ ≤ materialH y ^ γ * materialE0 y ^ A := by
  let A := 8 * |γ| * L * (1 + L) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, fun x y hx hy hxy => ?_⟩
  have hcube := cube_difference_le_materialE0Exponent hL hx hy hxy
  have hmul := mul_le_mul_of_nonneg_left hcube
    (show 0 ≤ |γ| * (2 / 3 : ℝ) from mul_nonneg (abs_nonneg _) (by norm_num))
  have habs : γ * (-2 / 3) * (x ^ 3 - y ^ 3) ≤
      |γ| * (2 / 3) * |x ^ 3 - y ^ 3| := by
    have h := le_abs_self (γ * (-2 / 3) * (x ^ 3 - y ^ 3))
    simpa only [abs_mul, abs_neg, abs_div, Nat.abs_ofNat] using h
  have hb : γ * (-2 / 3) * (x ^ 3 - y ^ 3) ≤ A * materialE0Exponent y := by
    exact habs.trans (hmul.trans_eq (by dsimp only [A]; ring))
  simp only [materialH, materialE0, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [hb]

/-- For an inverse height power only an upper coordinate displacement is
needed. Points farther from the endpoint already have a smaller weight. -/
theorem materialH_neg_rpow_oneSided_shift
    {β L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ y + L →
      materialH x ^ (-β) ≤ materialH y ^ (-β) * materialE0 y ^ A := by
  obtain ⟨A, hA, hb⟩ := materialH_rpow_bounded_shift (-β) hL
  refine ⟨A, hA, fun x y hx hy hxy => ?_⟩
  by_cases hyx : y ≤ x
  · apply hb x y hx hy
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith only [hxy]
  · have hxy' : x ≤ y := le_of_not_ge hyx
    have hcube := pow_le_pow_left₀ hx hxy' 3
    have hmul := mul_le_mul_of_nonneg_left hcube hβ
    have hE : 0 ≤ materialE0Exponent y := by
      have hh := one_add_sq_le_materialE0Exponent hy
      nlinarith only [hh, sq_nonneg (1 + y)]
    have hAE := mul_nonneg hA hE
    simp only [materialH, materialE0, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
    nlinarith only [hmul, hAE]

end ContinuousFlexibility.Analysis
