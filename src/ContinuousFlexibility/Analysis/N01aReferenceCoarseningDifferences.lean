module

public import ContinuousFlexibility.Analysis.N01aReferenceCoarseningNorms

/-!
# Actual source differences with measurable representatives

The frozen graph topology uses square norms of differences. The revised
local L² contract supplies signed measurability and is closed under
subtraction; the actual integral estimates retain their original form.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter

theorem n01a_localized_sub_square_le (χ a b : ℝ) :
    (χ * (a - b)) ^ 2 ≤ 2 * (χ * a) ^ 2 + 2 * (χ * b) ^ 2 := by
  nlinarith [sq_nonneg (χ * a + χ * b)]

theorem n01a_integrable_localized_sub_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {χ f g : Ω → ℝ}
    (hχ : AEMeasurable χ μ) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfi : Integrable (fun x => (χ x * f x) ^ 2) μ)
    (hgi : Integrable (fun x => (χ x * g x) ^ 2) μ) :
    Integrable (fun x => (χ x * (f x - g x)) ^ 2) μ ∧
      (∫ x, (χ x * (f x - g x)) ^ 2 ∂μ) ≤
        2 * (∫ x, (χ x * f x) ^ 2 ∂μ) + 2 * (∫ x, (χ x * g x) ^ 2 ∂μ) := by
  have hdom : Integrable (fun x => 2 * (χ x * f x) ^ 2 + 2 * (χ x * g x) ^ 2) μ :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hpoint (x : Ω) := n01a_localized_sub_square_le (χ x) (f x) (g x)
  have hm : AEMeasurable (fun x => (χ x * (f x - g x)) ^ 2) μ := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using (hχ.mul (hf.sub hg)).pow_const (2 : ℕ)
  have hi : Integrable (fun x => (χ x * (f x - g x)) ^ 2) μ :=
    hdom.mono_nonneg hm.aestronglyMeasurable
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hpoint)
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi hdom hpoint
  simpa only [integral_add (hfi.const_mul 2) (hgi.const_mul 2), integral_const_mul] using hb

theorem n01a_radialCellIntegrable_sub {D : ReferenceData} (hD : RadialPartition D)
    {f g : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hfm : AEMeasurable f (radialPhysicalMeasure D))
    (hgm : AEMeasurable g (radialPhysicalMeasure D)) :
    RadialCellIntegrable D (fun p => f p - g p) := by
  exact hf.sub hg

theorem n01a_referenceCellSquare_sub_le {D : ReferenceData} (hD : RadialPartition D)
    (hab : D.a ≤ D.b) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hfm : AEMeasurable f (radialPhysicalMeasure D))
    (hgm : AEMeasurable g (radialPhysicalMeasure D)) (i : ℕ) :
    referenceCellSquare D i (fun p => f p - g p) ≤
      2 * referenceCellSquare D i f + 2 * referenceCellSquare D i g := by
  have hi := n01a_radialCellIntegrable_sub hD hf hg hfm hgm
  have hb := (n01a_integrable_localized_sub_square
    ((hD.1 i).continuous.comp continuous_fst).measurable.aemeasurable hfm hgm
    (hf.integrable_square i) (hg.integrable_square i)).2
  rw [n01a_referenceCellSquare_eq_integral hab hi i, n01a_referenceCellSquare_eq_integral hab hf i,
    n01a_referenceCellSquare_eq_integral hab hg i]
  calc
    _ ≤ (2 * Real.pi)⁻¹ *
        (2 * (∫ p, (D.localizer i p.1 * f p) ^ 2 ∂radialPhysicalMeasure D) +
          2 * (∫ p, (D.localizer i p.1 * g p) ^ 2 ∂radialPhysicalMeasure D)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Measurable source representatives have square-integrable, summable differences.
No assertion about the mean of the difference is needed for this conclusion. -/
theorem n01a_source_difference_square_member {D : ReferenceData} (hD : RadialPartition D)
    (hab : D.a ≤ D.b) (γ M : ℝ) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hfm : AEMeasurable f (radialPhysicalMeasure D))
    (hgm : AEMeasurable g (radialPhysicalMeasure D))
    (hfs : Summable (sourceCellSquare D γ M f))
    (hgs : Summable (sourceCellSquare D γ M g)) :
    RadialCellIntegrable D (fun p => f p - g p) ∧
      Summable (sourceCellSquare D γ M (fun p => f p - g p)) := by
  refine ⟨n01a_radialCellIntegrable_sub hD hf hg hfm hgm, ?_⟩
  have hb (i : ℕ) : sourceCellSquare D γ M (fun p => f p - g p) i ≤
      2 * sourceCellSquare D γ M f i + 2 * sourceCellSquare D γ M g i := by
    calc
      _ ≤ Real.exp (2 * M * radialQ (D.cellIndex i) + 2 * γ * radialS (D.cellIndex i)) *
          (2 * referenceCellSquare D i f + 2 * referenceCellSquare D i g) :=
        mul_le_mul_of_nonneg_left
          (n01a_referenceCellSquare_sub_le hD hab hf hg hfm hgm i) (Real.exp_pos _).le
      _ = _ := by unfold sourceCellSquare; ring
  exact Summable.of_nonneg_of_le
    (fun i => n01a_sourceCellSquare_nonneg hab γ M (fun p => f p - g p) i) hb
    ((hfs.mul_left 2).add (hgs.mul_left 2))

end ContinuousFlexibility.Statements
