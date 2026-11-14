module

public import ContinuousFlexibility.Analysis.N05ReferenceZeroRemainder
public import ContinuousFlexibility.Radial.ReferenceWeightedMeasure
public import ContinuousFlexibility.Radial.ReferenceExponentComparison

/-!
# Increasing the output material loss for arbitrary physical jets

This inclusion uses only the actual localized square sum. It therefore
applies to odd jets and to first normal derivatives as well as to even
reference outputs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceOutput_weighted_mono {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ N M : ℝ}
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (referenceWeightedMeasure D γ (-N)))
    (hNM : N ≤ M) :
    MemLp f 2 (referenceWeightedMeasure D γ (-M)) ∧
      outputNormSquare D γ M 0 (f, 0) ≤ outputNormSquare D γ N 0 (f, 0) := by
  obtain ⟨hc, hs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hf
  rw [sourceCellSquare_neg_fun] at hs
  have hb (m : ℕ) : outputCellSquare D γ M f m ≤ outputCellSquare D γ N f m :=
    outputCellSquare_mono_weights hab hc le_rfl hNM m
  have hsum : Summable (outputCellSquare D γ M f) :=
    hs.of_nonneg_of_le (outputCellSquare_nonneg hab γ M hc) hb
  refine ⟨memLp_referenceWeightedMeasure hab hpart hc
    (by simpa only [sourceCellSquare_neg_fun] using hsum), ?_⟩
  simpa only [outputNormSquare, n05_outputRemainder_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hsum.tsum_le_tsum hb hs

end ContinuousFlexibility.Radial
