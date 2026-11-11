import ContinuousFlexibility.Radial.InnerWeightRatios
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth inner weights which are constant on the buffers

The logarithm is interpolated only between two prescribed walls. The
weight is exactly its endpoint value on each entire exterior buffer, so
the leading local Poisson term incurs no weight loss there. Logarithmic
convexity bounds the rest of the cell by the two endpoint comparisons.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

def innerWeightTransition (l r x : ℝ) : ℝ := smoothTransition ((x - l) / (r - l))

def innerInterpolatedWeight (l r u v x : ℝ) : ℝ :=
  exp ((1 - innerWeightTransition l r x) * log u + innerWeightTransition l r x * log v)

theorem innerWeightTransition_contDiff (l r : ℝ) :
    ContDiff ℝ ∞ (innerWeightTransition l r) :=
  smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem innerWeightTransition_nonneg (l r x : ℝ) : 0 ≤ innerWeightTransition l r x :=
  smoothTransition.nonneg _

theorem innerWeightTransition_le_one (l r x : ℝ) : innerWeightTransition l r x ≤ 1 :=
  smoothTransition.le_one _

theorem innerInterpolatedWeight_contDiff (l r u v : ℝ) :
    ContDiff ℝ ∞ (innerInterpolatedWeight l r u v) :=
  (((contDiff_const.sub (innerWeightTransition_contDiff l r)).mul contDiff_const).add
    ((innerWeightTransition_contDiff l r).mul contDiff_const)).exp

theorem innerInterpolatedWeight_pos (l r u v x : ℝ) : 0 < innerInterpolatedWeight l r u v x :=
  exp_pos _

/-- Both entire buffers, including their walls, have their exact endpoint
weight. The transition is confined to the open interval between them. -/
theorem innerInterpolatedWeight_eqOn_buffer {l r u v : ℝ}
    (hlr : l < r) (hu : 0 < u) (hv : 0 < v) (right : Bool) :
    EqOn (innerInterpolatedWeight l r u v) (fun _ => if right then v else u)
      (if right then Ici r else Iic l) := by
  intro x hx
  have hden : 0 < r - l := sub_pos.mpr hlr
  cases right with
  | false =>
    have hx' : x ≤ l := by simpa only [Bool.false_eq_true, ite_false, mem_Iic] using hx
    have hχ : innerWeightTransition l r x = 0 :=
      smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx') hden.le)
    simp only [innerInterpolatedWeight, hχ, sub_zero, one_mul, zero_mul, add_zero,
      exp_log hu, Bool.false_eq_true, ite_false]
  | true =>
    have hx' : r ≤ x := by simpa only [ite_true, mem_Ici] using hx
    have hχ : innerWeightTransition l r x = 1 :=
      smoothTransition.one_of_one_le ((le_div_iff₀ hden).mpr (by linarith only [hx']))
    simp only [innerInterpolatedWeight, hχ, sub_self, zero_mul, one_mul, zero_add,
      exp_log hv, ite_true]

/-- A leading function supported in either buffer sees an exactly
constant multiplier, for both signs and indeed every real exponent. -/
theorem innerInterpolatedWeight_mul_of_support_buffer {l r u v : ℝ}
    (hlr : l < r) (hu : 0 < u) (hv : 0 < v) (right : Bool) (σ : ℝ)
    (f : ℝ → ℝ) (hf : Function.support f ⊆ if right then Ici r else Iic l) (x : ℝ) :
    (innerInterpolatedWeight l r u v x) ^ σ * f x =
      (if right then v else u) ^ σ * f x := by
  by_cases hx : f x = 0
  · rw [hx, mul_zero, mul_zero]
  · rw [innerInterpolatedWeight_eqOn_buffer hlr hu hv right
      (hf (Function.mem_support.mpr hx))]

theorem innerInterpolatedWeight_log_ratio (l r : ℝ) {u v b : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hb : 0 < b) (x : ℝ) :
    log (innerInterpolatedWeight l r u v x / b) =
      (1 - innerWeightTransition l r x) * log (u / b) +
        innerWeightTransition l r x * log (v / b) := by
  rw [log_div (innerInterpolatedWeight_pos l r u v x).ne' hb.ne',
    innerInterpolatedWeight, log_exp, log_div hu.ne' hb.ne', log_div hv.ne' hb.ne']
  ring

/-- Convexity of the actual logarithmic interpolation keeps every
relative weight within the largest of the endpoint logarithmic bounds. -/
theorem innerInterpolatedWeight_abs_log_ratio_le (l r : ℝ) {u v b : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hb : 0 < b) (x : ℝ) :
    |log (innerInterpolatedWeight l r u v x / b)| ≤ max |log (u / b)| |log (v / b)| := by
  have hχ := innerWeightTransition_nonneg l r x
  have hχ' := sub_nonneg.mpr (innerWeightTransition_le_one l r x)
  rw [innerInterpolatedWeight_log_ratio l r hu hv hb]
  calc
    _ ≤ |(1 - innerWeightTransition l r x) * log (u / b)| +
        |innerWeightTransition l r x * log (v / b)| := abs_add_le _ _
    _ = (1 - innerWeightTransition l r x) * |log (u / b)| +
        innerWeightTransition l r x * |log (v / b)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hχ', abs_of_nonneg hχ]
    _ ≤ (1 - innerWeightTransition l r x) * max |log (u / b)| |log (v / b)| +
        innerWeightTransition l r x * max |log (u / b)| |log (v / b)| :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hχ')
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hχ)
    _ = _ := by ring

/-- Taking either sign does not change the endpoint envelope. -/
theorem innerInterpolatedWeight_signed_abs_log_ratio_le (l r : ℝ) {u v b σ : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hb : 0 < b) (hσ : |σ| ≤ 1) (x : ℝ) :
    |log ((innerInterpolatedWeight l r u v x) ^ σ / b ^ σ)| ≤
      max |log (u / b)| |log (v / b)| := by
  have hW := innerInterpolatedWeight_pos l r u v x
  have hlog : log ((innerInterpolatedWeight l r u v x) ^ σ / b ^ σ) =
      σ * log (innerInterpolatedWeight l r u v x / b) := by
    rw [log_div (rpow_pos_of_pos hW σ).ne' (rpow_pos_of_pos hb σ).ne',
      log_rpow hW, log_rpow hb, log_div hW.ne' hb.ne']
    ring
  rw [hlog, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hσ).trans
    (innerInterpolatedWeight_abs_log_ratio_le l r hu hv hb x)

/-- Each interpolated weight and its reciprocal are bounded on the whole
real line, by constants depending only on the two endpoint values. -/
theorem innerInterpolatedWeight_bounds (l r : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (x : ℝ) :
    innerInterpolatedWeight l r u v x ≤ exp (max |log u| |log v|) ∧
      (innerInterpolatedWeight l r u v x)⁻¹ ≤ exp (max |log u| |log v|) := by
  have h : |log (innerInterpolatedWeight l r u v x)| ≤ max |log u| |log v| := by
    simpa only [div_one] using
      innerInterpolatedWeight_abs_log_ratio_le l r hu hv (by norm_num : (0 : ℝ) < 1) x
  constructor
  · calc
      _ = exp (log (innerInterpolatedWeight l r u v x)) :=
        (exp_log (innerInterpolatedWeight_pos l r u v x)).symm
      _ ≤ _ := exp_le_exp.mpr (abs_le.mp h).2
  · calc
      _ = exp (-log (innerInterpolatedWeight l r u v x)) := by
        rw [exp_neg, exp_log (innerInterpolatedWeight_pos l r u v x)]
      _ ≤ _ := exp_le_exp.mpr (by linarith only [(abs_le.mp h).1])

theorem innerGeometricMeanWeight_abs_log_ratio {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (right : Bool) :
    |log (innerGeometricMeanWeight u v / (if right then v else u))| =
      (1 / 2 : ℝ) * |log (v / u)| := by
  rw [innerGeometricMeanWeight_log_ratio hu hv right, abs_mul]
  have h : |if right then -(1 / 2 : ℝ) else 1 / 2| = 1 / 2 := by
    cases right <;> norm_num
  rw [h]

/-- Interpolating the two neighboring gap weights costs at most half of
the larger adjacent logarithmic ratio relative to the cell's own weight. -/
theorem innerInterpolatedWeight_geometric_log_bound (l r : ℝ) {u v w σ : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hσ : |σ| ≤ 1) (x : ℝ) :
    |log ((innerInterpolatedWeight l r (innerGeometricMeanWeight u v)
      (innerGeometricMeanWeight v w) x) ^ σ / v ^ σ)| ≤
        (1 / 2 : ℝ) * max |log (v / u)| |log (w / v)| := by
  have hleft : |log (innerGeometricMeanWeight u v / v)| = (1 / 2 : ℝ) * |log (v / u)| := by
    simpa only [ite_true] using innerGeometricMeanWeight_abs_log_ratio hu hv true
  have hright : |log (innerGeometricMeanWeight v w / v)| = (1 / 2 : ℝ) * |log (w / v)| := by
    simpa only [Bool.false_eq_true, ite_false] using
      innerGeometricMeanWeight_abs_log_ratio hv hw false
  calc
    _ ≤ max |log (innerGeometricMeanWeight u v / v)|
        |log (innerGeometricMeanWeight v w / v)| :=
      innerInterpolatedWeight_signed_abs_log_ratio_le l r
        (innerGeometricMeanWeight_pos hu hv) (innerGeometricMeanWeight_pos hv hw) hv hσ x
    _ ≤ _ := by
      rw [hleft, hright]
      exact max_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

/-- For the actual three neighboring cell weights, the interpolation has
only a fixed coefficient-power logarithmic loss, uniformly for both signs. -/
theorem innerInterpolatedWeight_cell_coefficient_bound (N : ℕ) (l r : ℝ)
    {a γ σ : ℝ} (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    |log ((innerInterpolatedWeight l r
      (innerGeometricMeanWeight (innerCellWeight N a γ (m - 1)) (innerCellWeight N a γ m))
      (innerGeometricMeanWeight (innerCellWeight N a γ m) (innerCellWeight N a γ (m + 1))) x) ^ σ /
        (innerCellWeight N a γ m) ^ σ)| ≤ 16 * (1 + a) * radialQ m := by
  have hprev : 1 ≤ m - 1 := by omega
  have hsucc : m - 1 + 1 = m := by omega
  have hleft : |log (innerCellWeight N a γ m / innerCellWeight N a γ (m - 1))| ≤
      32 * (1 + a) * radialQ (m - 1) := by
    simpa only [Real.rpow_one, hsucc] using
      innerCellWeight_signed_log_coefficient_le N ha hγ (by norm_num : |(1 : ℝ)| ≤ 1) hprev
  have hright : |log (innerCellWeight N a γ (m + 1) / innerCellWeight N a γ m)| ≤
      32 * (1 + a) * radialQ m := by
    simpa only [Real.rpow_one] using
      innerCellWeight_signed_log_coefficient_le N ha hγ (by norm_num : |(1 : ℝ)| ≤ 1)
        (show 1 ≤ m by omega)
  have hleft' := hleft.trans (mul_le_mul_of_nonneg_left
    (radialQ_monotone (Nat.sub_le m 1)) (by positivity : 0 ≤ 32 * (1 + a)))
  calc
    _ ≤ (1 / 2 : ℝ) * max
        |log (innerCellWeight N a γ m / innerCellWeight N a γ (m - 1))|
        |log (innerCellWeight N a γ (m + 1) / innerCellWeight N a γ m)| :=
      innerInterpolatedWeight_geometric_log_bound l r (innerCellWeight_pos N a γ (m - 1))
        (innerCellWeight_pos N a γ m) (innerCellWeight_pos N a γ (m + 1)) hσ x
    _ ≤ (1 / 2 : ℝ) * (32 * (1 + a) * radialQ m) :=
      mul_le_mul_of_nonneg_left (max_le hleft' hright) (by norm_num)
    _ = _ := by ring

end ContinuousFlexibility.Radial
