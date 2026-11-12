import ContinuousFlexibility.Analysis.N05CanonicalCutoffNormalJet
import ContinuousFlexibility.Analysis.N05ReferenceFullAngularSobolev

/-!
# The normal cutoff correction in every physical output weight

The prescribed cutoff derivative has compact radial support. Its fixed
weighted square costs only the square of the same left scalar already
included in the original reference output norm.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open ContinuousFlexibility.Radial

theorem n05_leftCutoff_normal_weighted_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {χ : ℝ → ℝ} (hχ : CutoffConditions D χ)
    (γ M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, ∀ ur : PolarPoint → ℝ,
      MemLp ur 2 (referenceWeightedMeasure D γ (-M)) →
      MemLp (fun p => ur p - a * deriv χ p.1) 2 (referenceWeightedMeasure D γ (-M)) ∧
      outputNormSquare D γ M 0 ((fun p => ur p - a * deriv χ p.1), 0) ≤
        C * (outputNormSquare D γ M 0 (ur, 0) + a ^ 2) := by
  have hab := hD.choose_spec.1.2.1.le
  have hpart := hD.choose_spec.2.1
  obtain ⟨hc, hs⟩ := n05_leftCutoff_deriv_output_weights hD hχ γ M
  let d : PolarPoint → ℝ := fun p => deriv χ p.1
  have hd : MemLp d 2 (referenceWeightedMeasure D γ (-M)) :=
    memLp_referenceWeightedMeasure hab hpart hc (by simpa only [sourceCellSquare_neg_fun] using hs)
  let Z : ℝ := outputNormSquare D γ M 0 (d, 0)
  have hZ : 0 ≤ Z := by
    rw [n05_referenceZeroOutputNormSquare_eq_integral hab hpart hd]
    exact integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨2 * (1 + Z), by positivity, fun a ur hur => ?_⟩
  have hscaled : MemLp (fun p => -a * d p) 2 (referenceWeightedMeasure D γ (-M)) :=
    hd.const_mul (-a)
  have heq : (fun p => ur p - a * deriv χ p.1) = ur + (fun p => -a * d p) := by
    funext p
    change ur p - a * d p = ur p + -a * d p
    ring
  have hscaledNorm : outputNormSquare D γ M 0 ((fun p => -a * d p), 0) = a ^ 2 * Z := by
    rw [n05_referenceZeroOutputNormSquare_eq_integral hab hpart hscaled]
    dsimp only [Z]
    rw [n05_referenceZeroOutputNormSquare_eq_integral hab hpart hd]
    simp_rw [mul_pow, neg_sq]
    rw [integral_const_mul]
  have huNonneg : 0 ≤ outputNormSquare D γ M 0 (ur, 0) := by
    rw [n05_referenceZeroOutputNormSquare_eq_integral hab hpart hur]
    exact integral_nonneg (fun _ => sq_nonneg _)
  rw [heq]
  refine ⟨hur.add hscaled, ?_⟩
  have hb := n05_referenceZeroOutputNormSquare_add_le hab hpart hur hscaled
  rw [hscaledNorm] at hb
  apply hb.trans
  nlinarith only [huNonneg, hZ, sq_nonneg a, mul_nonneg hZ huNonneg]

end ContinuousFlexibility.Statements
