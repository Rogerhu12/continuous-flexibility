import ContinuousFlexibility.Analysis.OneHighFrequencyEmbedding
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

/-!
# Square-integrable inverse weights on circle frequencies

The frequency spacing is any positive real number `q`. In the physical circle
of period `P` it is `2 * π / P`; keeping it explicit also permits its use in
the mixed continuous/discrete Fourier measure of a cylinder.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

/-- The inverse square of the physical Bessel weight is summable on all
integer modes, including the zero mode. -/
theorem summable_circleInverseWeightSq {q : ℝ} (hq : 0 < q) :
    Summable (fun n : ℤ => 1 / (1 + (q * (n : ℝ)) ^ 2)) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine (hp.mul_left (1 / q ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hqn : 0 < (q * (n : ℝ)) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero hq.ne' hn0)
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (1 + (q * (n : ℝ)) ^ 2))]
  calc
    1 / (1 + (q * (n : ℝ)) ^ 2) ≤ 1 / (q * (n : ℝ)) ^ 2 :=
      one_div_le_one_div_of_le hqn (by linarith)
    _ = (1 / q ^ 2) * (1 / (n : ℝ) ^ 2) := by
      rw [mul_pow, one_div_mul_one_div]

/-- The squared real inverse Bessel weight has the rational expression
used in the summability comparison. -/
theorem circleInverseWeight_sq (q : ℝ) (n : ℤ) :
    (Real.sqrt (1 + (q * (n : ℝ)) ^ 2) ^ (-1 : ℝ)) ^ 2 =
      1 / (1 + (q * (n : ℝ)) ^ 2) := by
  rw [Real.rpow_neg_one, inv_pow, Real.sq_sqrt (by positivity), one_div]

/-- The inverse Bessel weight belongs to `L²` for counting measure. -/
theorem memLp_circleInverseWeight {q : ℝ} (hq : 0 < q) :
    MemLp (fun n : ℤ => Real.sqrt (1 + (q * (n : ℝ)) ^ 2) ^ (-1 : ℝ))
      2 Measure.count := by
  apply (memLp_two_iff_integrable_sq
    (measurable_of_countable _).aestronglyMeasurable).mpr
  apply integrable_count_iff.mpr
  refine (summable_circleInverseWeightSq hq).congr fun n => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _), circleInverseWeight_sq]

end ContinuousFlexibility.Analysis
