import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Radial.R11bCompactSources
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Changing to the physical-space left cutoff

The reference inverse uses `D.chiLeft`; the canonical representation uses
the cutoff in the physical spaces. Their difference is supported away from
both endpoints inside the physical core and belongs to every cell weight.
This permits the same left constant to be used with either cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Radial

theorem n05_leftCutoff_difference_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ radialCore D ∧
      ∀ r ∈ radialCore D, r ∉ J → D.chiLeft r - χ r = 0 := by
  obtain ⟨ε, hε, hleft, hright⟩ := hborder.2.2.2.2.2
  obtain ⟨δ, hδ, _, hχleft, hχright⟩ := hχ.2.1
  let d : ℝ := min ε δ
  have hd : 0 < d := lt_min hε hδ
  refine ⟨Icc (D.a + d) (D.b - d), isCompact_Icc, ?_, ?_⟩
  · intro r hr
    exact ⟨by linarith only [hr.1, hd], by linarith only [hr.2, hd]⟩
  · intro r hr hout
    have hcases : r < D.a + d ∨ D.b - d < r := by
      by_cases hl : D.a + d ≤ r
      · exact Or.inr (lt_of_not_ge (fun hh => hout ⟨hl, hh⟩))
      · exact Or.inl (lt_of_not_ge hl)
    rcases hcases with hl | hr'
    · have hε' : r < D.a + ε :=
        hl.trans_le (add_le_add_left (min_le_left ε δ) D.a)
      have hδ' : r ≤ D.a + δ :=
        hl.le.trans (add_le_add_left (min_le_right ε δ) D.a)
      rw [hleft r ⟨hr.1, hε'⟩, hχleft r hδ', sub_self]
    · have hε' : D.b - ε < r :=
        (sub_le_sub_left (min_le_left ε δ) D.b).trans_lt hr'
      have hδ' : D.b - δ ≤ r :=
        (sub_le_sub_left (min_le_right ε δ) D.b).trans hr'.le
      rw [hright r ⟨hε', hr.2⟩, hχright r hδ', sub_self]

theorem n05_leftCutoff_difference_output_weights {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) (γ M : ℝ) :
    RadialCellIntegrable D (fun p => D.chiLeft p.1 - χ p.1) ∧
      Summable (outputCellSquare D γ M (fun p => D.chiLeft p.1 - χ p.1)) := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := n05_leftCutoff_difference_compact hD hborder hχ
  exact r11b_compact_output_cell_summable hD hJ hJcore
    ((hborder.2.2.2.2.1.continuous.sub hχ.1.continuous).comp continuous_fst)
    (fun r hr hnot _ => hzero r hr hnot) γ M

/-- The extra compact correction is controlled by the already included
left scalar, uniformly for all outputs at the selected exponents. -/
theorem n05_outputRemainder_cutoff_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {χ : ℝ → ℝ} (hχ : CutoffConditions D χ) (γ M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, ∀ U : RadialUnknown,
      OutputRealization D γ M a U →
      RadialCellIntegrable D (fun p => U.1 p - a * χ p.1) ∧
      Summable (outputCellSquare D γ M (fun p => U.1 p - a * χ p.1)) ∧
      (∑' m, outputCellSquare D γ M (fun p => U.1 p - a * χ p.1) m) ≤
        C * outputNormSquare D γ M a U := by
  obtain ⟨hf, hs⟩ := n05_leftCutoff_difference_output_weights hD hborder hχ γ M
  let f : PolarPoint → ℝ := fun p => D.chiLeft p.1 - χ p.1
  let Z : ℝ := ∑' m, outputCellSquare D γ M f m
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hZ : 0 ≤ Z := tsum_nonneg (fun m => outputCellSquare_nonneg hab γ M hf m)
  refine ⟨2 * (1 + Z), by positivity, fun a U hU => ?_⟩
  have hscaled := hf.const_mul a
  have hscaledSum := outputCellSquare_summable_const_mul hs a
  have heq : (fun p => U.1 p - a * χ p.1) =
      (fun p => outputRemainder D a U p + a * f p) := by
    funext p
    dsimp only [outputRemainder, f]
    ring
  have htotal : Summable (outputCellSquare D γ M
      (fun p => outputRemainder D a U p + a * f p)) :=
    outputCellSquare_summable_add hab hU.1 hscaled hU.2.1 hscaledSum
  rw [heq]
  refine ⟨hU.1.add hscaled, htotal, ?_⟩
  have hsum : (∑' m, outputCellSquare D γ M (fun p => a * f p) m) = a ^ 2 * Z := by
    simp_rw [outputCellSquare_const_mul]
    exact tsum_mul_left
  have hbound := htotal.tsum_le_tsum
    (fun m => outputCellSquare_add_le hab γ M m hU.1 hscaled)
    ((hU.2.1.add hscaledSum).mul_left 2)
  rw [tsum_mul_left, hU.2.1.tsum_add hscaledSum, hsum] at hbound
  have hR : 0 ≤ ∑' m, outputCellSquare D γ M (outputRemainder D a U) m :=
    tsum_nonneg (fun m => outputCellSquare_nonneg hab γ M hU.1 m)
  apply hbound.trans
  dsimp only [outputNormSquare]
  nlinarith only [hZ, hR, sq_nonneg a, sq_nonneg U.2,
    mul_nonneg hZ hR, mul_nonneg hZ (sq_nonneg U.2)]

end ContinuousFlexibility.Statements
