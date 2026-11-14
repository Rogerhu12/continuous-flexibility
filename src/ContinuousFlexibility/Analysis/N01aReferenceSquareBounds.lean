module

public import ContinuousFlexibility.Analysis.N01aReferencePartitionSquares

/-!
# Physical square bounds and scalar convergence for reference graphs
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem sourceNormSquare_scalar_le {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (F : RadialSource) : F.2 ^ 2 ≤ sourceNormSquare D γ M F := by
  unfold sourceNormSquare
  exact le_add_of_nonneg_right (tsum_nonneg fun m => n01a_sourceCellSquare_nonneg hab γ M F.1 m)

theorem outputNormSquare_scalar_le {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M aL : ℝ) (U : RadialUnknown) : U.2 ^ 2 ≤ outputNormSquare D γ M aL U := by
  have hs : 0 ≤ ∑' m : ℕ, outputCellSquare D γ M (outputRemainder D aL U) m :=
    tsum_nonneg fun m => n01a_outputCellSquare_nonneg hab γ M (outputRemainder D aL U) m
  unfold outputNormSquare
  linarith only [sq_nonneg aL, hs]

theorem exists_source_physical_square_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : RadialSource, SourceMember D γ M F →
      Integrable (fun p => F.1 p ^ 2) (radialPhysicalMeasure D) ∧
        (∫ p, F.1 p ^ 2 ∂radialPhysicalMeasure D) ≤ C * sourceNormSquare D γ M F := by
  obtain ⟨C₁, hC₁, hpart⟩ := exists_radialPartition_integral_square_bound hab hD
  obtain ⟨C₂, hC₂, hweight⟩ := exists_source_cell_square_bound hab hγ M
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, fun F hF => ?_⟩
  obtain ⟨hs, hsum⟩ := hweight F.1 hF.2.1
  obtain ⟨hi, hb⟩ := hpart F.1 hF.1 hs
  refine ⟨hi, ?_⟩
  have hrow : (∑' m, sourceCellSquare D γ M F.1 m) ≤ sourceNormSquare D γ M F := by
    unfold sourceNormSquare
    exact le_add_of_nonneg_left (sq_nonneg F.2)
  calc
    _ ≤ C₁ * (∑' m, referenceCellSquare D m F.1) := hb
    _ ≤ C₁ * (C₂ * ∑' m, sourceCellSquare D γ M F.1 m) :=
      mul_le_mul_of_nonneg_left hsum hC₁.le
    _ ≤ C₁ * (C₂ * sourceNormSquare D γ M F) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrow hC₂.le) hC₁.le
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_output_physical_square_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RadialUnknown) (aL : ℝ), OutputRealization D γ M aL U →
      Integrable (fun p => outputRemainder D aL U p ^ 2) (radialPhysicalMeasure D) ∧
        (∫ p, outputRemainder D aL U p ^ 2 ∂radialPhysicalMeasure D) ≤
          C * outputNormSquare D γ M aL U := by
  obtain ⟨C₁, hC₁, hpart⟩ := exists_radialPartition_integral_square_bound hab hD
  obtain ⟨C₂, hC₂, hweight⟩ := exists_output_cell_square_bound hab hγ M
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, fun U aL hU => ?_⟩
  obtain ⟨hs, hsum⟩ := hweight (outputRemainder D aL U) hU.2.1
  obtain ⟨hi, hb⟩ := hpart (outputRemainder D aL U) hU.1 hs
  refine ⟨hi, ?_⟩
  have hrow : (∑' m, outputCellSquare D γ M (outputRemainder D aL U) m) ≤
      outputNormSquare D γ M aL U := by
    unfold outputNormSquare
    linarith only [sq_nonneg aL, sq_nonneg U.2]
  calc
    _ ≤ C₁ * (∑' m, referenceCellSquare D m (outputRemainder D aL U)) := hb
    _ ≤ C₁ * (C₂ * ∑' m, outputCellSquare D γ M (outputRemainder D aL U) m) :=
      mul_le_mul_of_nonneg_left hsum hC₁.le
    _ ≤ C₁ * (C₂ * outputNormSquare D γ M aL U) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrow hC₂.le) hC₁.le
    _ = _ := (mul_assoc _ _ _).symm

private theorem n01a_tendsto_zero_of_square_bound {f g : ℕ → ℝ}
    (hfg : ∀ n, f n ^ 2 ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => f n ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => sq_nonneg (f n))
      (Eventually.of_forall hfg) hg
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsq.sqrt

theorem tendsto_source_scalar_of_normSquare {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (F : ℕ → RadialSource)
    (hF : Tendsto (fun n => sourceNormSquare D γ M (F n)) atTop (𝓝 0)) :
    Tendsto (fun n => (F n).2) atTop (𝓝 0) :=
  n01a_tendsto_zero_of_square_bound (fun n => sourceNormSquare_scalar_le hab γ M (F n)) hF

theorem tendsto_output_scalar_of_normSquare {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (U : ℕ → RadialUnknown) (aL : ℕ → ℝ)
    (hU : Tendsto (fun n => outputNormSquare D γ M (aL n) (U n)) atTop (𝓝 0)) :
    Tendsto (fun n => (U n).2) atTop (𝓝 0) :=
  n01a_tendsto_zero_of_square_bound
    (fun n => outputNormSquare_scalar_le hab γ M (aL n) (U n)) hU

theorem tendsto_source_physical_square_of_normSquare {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ : ℝ} (hγ : 0 < γ) (M : ℝ)
    (F : ℕ → RadialSource) (hF : ∀ n, SourceMember D γ M (F n))
    (hlim : Tendsto (fun n => sourceNormSquare D γ M (F n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p, (F n).1 p ^ 2 ∂radialPhysicalMeasure D) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_source_physical_square_bound hab hD hγ M
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
    (Eventually.of_forall fun n => (hb (F n) (hF n)).2)
  simpa only [mul_zero] using hlim.const_mul C

end ContinuousFlexibility.Statements
