import ContinuousFlexibility.Analysis.RootSmoothHeight
import ContinuousFlexibility.Analysis.RootChartSymmetry

/-!
# Actual positive value intervals at the root

The boundary identities give B = h′² and α = a ((3χ/2)^(2/3))/h′.
Consequently fixed positive intervals for the original coefficient and
the true odd root value, together with h′ ∈ [1/4,4], supply all value
intervals used in the height-jet composition estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem rootHeightFactor_value_bounds
    {a χ k al au χl χu : ℝ} (hal : 0 < al) (hχl : 0 < χl)
    (ha : a ∈ Icc al au) (hχ : χ ∈ Icc χl χu) (hk : k ∈ Icc (1 / 4 : ℝ) 4) :
    a * ((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ) / k ∈
      Icc (al * ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) / 4)
        (4 * au * ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ)) := by
  have ha0 : 0 < a := hal.trans_le ha.1
  have hau : 0 < au := ha0.trans_le ha.2
  have hχ0 : 0 < χ := hχl.trans_le hχ.1
  have hχu : 0 < χu := hχ0.trans_le hχ.2
  have hk0 : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hfl : 0 < ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hχl) _
  have hfu : 0 < ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hχu) _
  have hf0 : 0 < ((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hχ0) _
  have hflower : ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) ≤
      ((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) hχl.le)
      (mul_le_mul_of_nonneg_left hχ.1 (by norm_num)) (by norm_num)
  have hfupper : ((3 / 2 : ℝ) * χ) ^ (2 / 3 : ℝ) ≤
      ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) hχ0.le)
      (mul_le_mul_of_nonneg_left hχ.2 (by norm_num)) (by norm_num)
  have hnl := mul_le_mul ha.1 hflower hfl.le ha0.le
  have hnu := mul_le_mul ha.2 hfupper hf0.le hau.le
  constructor
  · apply (le_div_iff₀ hk0).mpr
    have hm := mul_le_mul_of_nonneg_left hk.2
      (div_nonneg (mul_nonneg hal.le hfl.le) (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith only [hm, hnl]
  · apply (div_le_iff₀ hk0).mpr
    have hm := mul_le_mul_of_nonneg_left hk.1
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hau.le) hfu.le)
    nlinarith only [hm, hnu]

theorem rootBoundary_positive_value_intervals
    {G : ℝ × ℝ × ℝ → ℝ} {a : PolarPoint → ℝ} {h : ℝ → ℝ} {θ k : ℝ}
    {al au χl χu : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hperiod : ∀ x ζ η, G (x, ζ, η + Real.pi) = G (x, ζ, η) + Real.pi)
    (hzero : ∀ η, G (0, 0, η) = h η) (hderiv : HasDerivAt h k θ)
    (hk : k ∈ Icc (1 / 4 : ℝ) 4)
    (ha : ContDiffAt ℝ ∞ a (0, θ)) (hal : 0 < al)
    (havalue : a (0, θ) ∈ Icc al au) (hχl : 0 < χl)
    (hχvalue : extendedRootOddCoefficient G (0, θ) ∈ Icc χl χu) :
    rootAngularProduct G (0, θ) ∈ Icc (1 / 16 : ℝ) 16 ∧
      rootHeightFactor a G (0, θ) ∈
        Icc (al * ((3 / 2 : ℝ) * χl) ^ (2 / 3 : ℝ) / 4)
          (4 * au * ((3 / 2 : ℝ) * χu) ^ (2 / 3 : ℝ)) := by
  have hφperiod : ∀ r, 0 ≤ r → ∀ η,
      rootEven G (r, η + Real.pi) = rootEven G (r, η) + Real.pi :=
    fun r _ η => rootEven_period_add hperiod r η
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hperiod r
  have hχraw : rootOddCoefficient G (0, θ) ∈ Icc χl χu := by
    simpa only [extendedRootOddCoefficient_of_nonneg G
      (p := (0, θ)) (le_refl (0 : ℝ))] using hχvalue
  have hk0 : 0 < k := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hk.1
  have hχ0 : 0 < rootOddCoefficient G (0, θ) := hχl.trans_le hχraw.1
  have hαeq := (rootSmoothHeight_boundary hG Real.pi_ne_zero hχperiod hφperiod
    hzero hderiv hk0 hχ0 ha (hal.trans_le havalue.1)).1
  constructor
  · rw [rootAngularProduct_zero hG Real.pi_ne_zero hφperiod hzero hderiv]
    have hlo := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hk0.le).mpr hk.1
    have hhi := (sq_le_sq₀ hk0.le (by norm_num : (0 : ℝ) ≤ 4)).mpr hk.2
    norm_num at hlo hhi ⊢
    exact ⟨hlo, hhi⟩
  · rw [hαeq]
    exact rootHeightFactor_value_bounds hal hχl havalue hχraw hk

end ContinuousFlexibility.Analysis
