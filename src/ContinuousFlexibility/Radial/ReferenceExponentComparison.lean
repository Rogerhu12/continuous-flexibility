import ContinuousFlexibility.Radial.ReferenceCellL2
import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Inclusion of the reference domains at different exponents

The source and output domains are nested in the endpoint exponent.
Coefficient powers have opposite signs in the two norms. In particular,
raising the output coefficient loss enlarges the output domain; it does
not by itself transfer uniqueness of the maximal graph.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Radial

theorem sourceCellSquare_mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    {γ δ M N : ℝ} (hγ : γ ≤ δ) (hM : M ≤ N) (m : ℕ) :
    sourceCellSquare D γ M f m ≤ sourceCellSquare D δ N f m := by
  unfold sourceCellSquare
  apply mul_le_mul_of_nonneg_right ?_ (referenceCellSquare_nonneg hab m hf)
  apply Real.exp_le_exp.mpr
  have hq := mul_le_mul_of_nonneg_right hM (radialQ_nonneg (D.cellIndex m))
  have hs := mul_le_mul_of_nonneg_right hγ (radialS_nonneg (D.cellIndex m))
  nlinarith only [hq, hs]

theorem outputCellSquare_mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    {γ δ M N : ℝ} (hγ : γ ≤ δ) (hM : N ≤ M) (m : ℕ) :
    outputCellSquare D γ M f m ≤ outputCellSquare D δ N f m := by
  unfold outputCellSquare
  apply mul_le_mul_of_nonneg_right ?_ (referenceCellSquare_nonneg hab m hf)
  apply Real.exp_le_exp.mpr
  have hq := mul_le_mul_of_nonneg_right hM (radialQ_nonneg (D.cellIndex m))
  have hs := mul_le_mul_of_nonneg_right hγ (radialS_nonneg (D.cellIndex m))
  nlinarith only [hq, hs]

theorem SourceMember.mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ δ M N : ℝ} {F : RadialSource} (hF : SourceMember D δ N F)
    (hγ : γ ≤ δ) (hM : M ≤ N) : SourceMember D γ M F := by
  refine ⟨hF.1, ?_, hF.2.2⟩
  exact Summable.of_nonneg_of_le (sourceCellSquare_nonneg hab γ M hF.1)
    (sourceCellSquare_mono_weights hab hF.1 hγ hM) hF.2.1

theorem OutputRealization.mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ δ M N aL : ℝ} {U : RadialUnknown} (hU : OutputRealization D δ N aL U)
    (hγ : γ ≤ δ) (hM : N ≤ M) : OutputRealization D γ M aL U := by
  refine ⟨hU.1, ?_, hU.2.2⟩
  exact Summable.of_nonneg_of_le (outputCellSquare_nonneg hab γ M hU.1)
    (outputCellSquare_mono_weights hab hU.1 hγ hM) hU.2.1

theorem OutputMember.mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ δ M N : ℝ} {U : RadialUnknown} (hU : OutputMember D δ N U)
    (hγ : γ ≤ δ) (hM : N ≤ M) : OutputMember D γ M U := by
  obtain ⟨aL, haL⟩ := hU
  exact ⟨aL, haL.mono_weights hab hγ hM⟩

theorem sourceNormSquare_mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ δ M N : ℝ} {F : RadialSource} (hF : SourceMember D δ N F)
    (hγ : γ ≤ δ) (hM : M ≤ N) :
    sourceNormSquare D γ M F ≤ sourceNormSquare D δ N F := by
  exact add_le_add_left
    (Summable.tsum_le_tsum (sourceCellSquare_mono_weights hab hF.1 hγ hM)
      (hF.mono_weights hab hγ hM).2.1 hF.2.1) _

theorem outputNormSquare_mono_weights {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ δ M N aL : ℝ} {U : RadialUnknown} (hU : OutputRealization D δ N aL U)
    (hγ : γ ≤ δ) (hM : N ≤ M) :
    outputNormSquare D γ M aL U ≤ outputNormSquare D δ N aL U := by
  exact add_le_add_left
    (Summable.tsum_le_tsum (outputCellSquare_mono_weights hab hU.1 hγ hM)
      (hU.mono_weights hab hγ hM).2.1 hU.2.1) _

theorem sourceNormSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) :
    0 ≤ sourceNormSquare D γ M F :=
  add_nonneg (sq_nonneg _) (tsum_nonneg (sourceCellSquare_nonneg hab γ M hF.1))

theorem outputNormSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M aL : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M aL U) :
    0 ≤ outputNormSquare D γ M aL U :=
  add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (tsum_nonneg (outputCellSquare_nonneg hab γ M hU.1))

/-- Lowering the endpoint exponent preserves every equation in the maximal graph. -/
theorem ReferenceGraph.lower_exponent {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ δ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (h : ReferenceGraph D δ M₀ M₁ U F) (hγ : γ ≤ δ) :
    ReferenceGraph D γ M₀ M₁ U F :=
  ⟨h.1.mono_weights hab hγ le_rfl,
    h.2.1.mono_weights hab hγ le_rfl, h.2.2⟩

theorem RadialRepresentativeEq.refl (D : ReferenceData) (U : RadialUnknown) :
    RadialRepresentativeEq D U U := ⟨rfl, Filter.EventuallyEq.rfl⟩

theorem RadialRepresentativeEq.symm {D : ReferenceData} {U V : RadialUnknown}
    (h : RadialRepresentativeEq D U V) : RadialRepresentativeEq D V U :=
  ⟨h.1.symm, h.2.symm⟩

theorem RadialRepresentativeEq.trans {D : ReferenceData} {U V W : RadialUnknown}
    (hUV : RadialRepresentativeEq D U V) (hVW : RadialRepresentativeEq D V W) :
    RadialRepresentativeEq D U W := ⟨hUV.1.trans hVW.1, hUV.2.trans hVW.2⟩

end ContinuousFlexibility.Statements
