import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The decay supplied by the two actual height weights

Using the smaller of the two neighboring weighted bounds produces decay
in the difference of logarithmic heights. The prefactor is retained
exactly, so the estimate can be applied before any material absorption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

theorem n07a_weightRatio_exp {Hk Hm : ℝ} (hk : 0 < Hk) (hm : 0 < Hm)
    (A β γ : ℝ) :
    (A * Hk ^ γ / Hk ^ β) * (Hm ^ β / Hm ^ γ) =
      A * Real.exp ((γ - β) * (Real.log Hk - Real.log Hm)) := by
  calc
    _ = A * ((Hk ^ γ / Hk ^ β) * (Hm ^ β / Hm ^ γ)) := by ring
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos hk, Real.rpow_def_of_pos hk,
        Real.rpow_def_of_pos hm, Real.rpow_def_of_pos hm,
        ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring

theorem n07a_twoWeightRatio_min {Hk Hm A δ : ℝ}
    (hk : 0 < Hk) (hm : 0 < Hm) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (β : ℝ) :
    min ((A * Hk ^ (β - δ) / Hk ^ β) * (Hm ^ β / Hm ^ (β - δ)))
      ((A * Hk ^ (β + δ) / Hk ^ β) * (Hm ^ β / Hm ^ (β + δ))) =
      A * Real.exp (-δ * |Real.log Hk - Real.log Hm|) := by
  rw [n07a_weightRatio_exp hk hm, n07a_weightRatio_exp hk hm,
    show β - δ - β = -δ by ring, show β + δ - β = δ by ring]
  by_cases hd : 0 ≤ Real.log Hk - Real.log Hm
  · have he : Real.exp (-δ * (Real.log Hk - Real.log Hm)) ≤
        Real.exp (δ * (Real.log Hk - Real.log Hm)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hδ hd]
    rw [min_eq_left (mul_le_mul_of_nonneg_left he hA), abs_of_nonneg hd]
  · have hd' : Real.log Hk - Real.log Hm ≤ 0 := le_of_not_ge hd
    have he : Real.exp (δ * (Real.log Hk - Real.log Hm)) ≤
        Real.exp (-δ * (Real.log Hk - Real.log Hm)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hδ hd']
    rw [min_eq_right (mul_le_mul_of_nonneg_left he hA), abs_of_nonpos hd']
    congr 2
    ring

end ContinuousFlexibility.Analysis
