import ContinuousFlexibility.Radial.R11bWeightEmbedding

/-!
# Monotonicity in the reference coefficient exponents

At a fixed attenuation exponent, increasing the source coefficient exponent
strengthens the source norm. Increasing the output coefficient exponent
weakens the output norm and keeps the same left constant.

The maximum graph has a larger output domain after the latter change.
Accordingly, transporting the full inverse specification below requires a
separate uniqueness hypothesis on the new graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real MeasureTheory
open ContinuousFlexibility.Statements

theorem r11b_sourceCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (f : PolarPoint → ℝ) (m : ℕ) :
    0 ≤ sourceCellSquare D γ M f m := by
  unfold sourceCellSquare
  exact mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab m f)

theorem r11b_outputCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (f : PolarPoint → ℝ) (m : ℕ) :
    0 ≤ outputCellSquare D γ M f m := by
  unfold outputCellSquare
  exact mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab m f)

theorem r11b_sourceCellSquare_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) (f : PolarPoint → ℝ) (m : ℕ) :
    sourceCellSquare D γ Mlo f m ≤ sourceCellSquare D γ Mhi f m := by
  unfold sourceCellSquare
  apply mul_le_mul_of_nonneg_right ?_ (r11b_referenceCellSquare_nonneg hab m f)
  apply exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hM (radialQ_nonneg (D.cellIndex m))
  nlinarith

theorem r11b_outputCellSquare_antitone {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) (f : PolarPoint → ℝ) (m : ℕ) :
    outputCellSquare D γ Mhi f m ≤ outputCellSquare D γ Mlo f m := by
  unfold outputCellSquare
  apply mul_le_mul_of_nonneg_right ?_ (r11b_referenceCellSquare_nonneg hab m f)
  apply exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hM (radialQ_nonneg (D.cellIndex m))
  nlinarith

/-- Membership and the norm both transfer from a stronger source weight. -/
theorem r11b_source_coefficient_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {F : RadialSource}
    (hF : SourceMember D γ Mhi F) :
    SourceMember D γ Mlo F ∧
      sourceNormSquare D γ Mlo F ≤ sourceNormSquare D γ Mhi F := by
  have hmono := r11b_sourceCellSquare_mono hab (γ := γ) hM F.1
  have hs : Summable (sourceCellSquare D γ Mlo F.1) :=
    Summable.of_nonneg_of_le
      (r11b_sourceCellSquare_nonneg hab γ Mlo F.1) hmono hF.2.1
  refine ⟨⟨hF.1, hs, hF.2.2⟩, ?_⟩
  unfold sourceNormSquare
  exact add_le_add le_rfl (Summable.tsum_le_tsum hmono hs hF.2.1)

theorem r11b_sourceMember_of_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {F : RadialSource}
    (hF : SourceMember D γ Mhi F) : SourceMember D γ Mlo F :=
  (r11b_source_coefficient_mono hab hM hF).1

theorem r11b_sourceNormSquare_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {F : RadialSource}
    (hF : SourceMember D γ Mhi F) :
    sourceNormSquare D γ Mlo F ≤ sourceNormSquare D γ Mhi F :=
  (r11b_source_coefficient_mono hab hM hF).2

/-- A larger output coefficient exponent preserves the left constant and
decreases the realized output norm. -/
theorem r11b_output_coefficient_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi aL : ℝ} (hM : Mlo ≤ Mhi) {U : RadialUnknown}
    (hU : OutputRealization D γ Mlo aL U) :
    OutputRealization D γ Mhi aL U ∧
      outputNormSquare D γ Mhi aL U ≤ outputNormSquare D γ Mlo aL U := by
  have hmono := r11b_outputCellSquare_antitone hab (γ := γ) hM
    (outputRemainder D aL U)
  have hs : Summable (outputCellSquare D γ Mhi (outputRemainder D aL U)) :=
    Summable.of_nonneg_of_le
      (r11b_outputCellSquare_nonneg hab γ Mhi (outputRemainder D aL U)) hmono hU.2.1
  refine ⟨⟨hU.1, hs, hU.2.2⟩, ?_⟩
  unfold outputNormSquare
  exact add_le_add le_rfl (Summable.tsum_le_tsum hmono hs hU.2.1)

theorem r11b_outputRealization_of_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi aL : ℝ} (hM : Mlo ≤ Mhi) {U : RadialUnknown}
    (hU : OutputRealization D γ Mlo aL U) : OutputRealization D γ Mhi aL U :=
  (r11b_output_coefficient_mono hab hM hU).1

theorem r11b_outputNormSquare_antitone {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi aL : ℝ} (hM : Mlo ≤ Mhi) {U : RadialUnknown}
    (hU : OutputRealization D γ Mlo aL U) :
    outputNormSquare D γ Mhi aL U ≤ outputNormSquare D γ Mlo aL U :=
  (r11b_output_coefficient_mono hab hM hU).2

theorem r11b_outputMember_of_le {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ Mlo Mhi : ℝ} (hM : Mlo ≤ Mhi) {U : RadialUnknown}
    (hU : OutputMember D γ Mlo U) : OutputMember D γ Mhi U := by
  obtain ⟨aL, haL⟩ := hU
  exact ⟨aL, r11b_outputRealization_of_le hab hM haL⟩

/-- The right-inverse property transports without a new uniqueness assertion. -/
theorem r11b_referenceInverse_right_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M₀ M₀' M₁ M₁' : ℝ} (h₀ : M₀ ≤ M₀') (h₁ : M₁ ≤ M₁')
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∀ F, SourceMember D γ M₀' F → ReferenceGraph D γ M₀' M₁' (G F) F := by
  intro F hF
  have h := hG.1 F (r11b_sourceMember_of_le hab h₀ hF)
  exact ⟨r11b_outputMember_of_le hab h₁ h.1, hF, h.2.2⟩

/-- Linearity and the old bound survive both weight changes. Uniqueness on
the enlarged output graph is supplied independently, never inferred from
coefficient-weight monotonicity. -/
theorem r11b_referenceInverseProperties_mono {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M₀ M₀' M₁ M₁' : ℝ} (h₀ : M₀ ≤ M₀') (h₁ : M₁ ≤ M₁')
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hunique : ∀ U F, ReferenceGraph D γ M₀' M₁' U F →
      RadialRepresentativeEq D (G F) U) :
    ReferenceInverseProperties D γ M₀' M₁' G := by
  refine ⟨r11b_referenceInverse_right_mono hab h₀ h₁ hG, hunique, ?_, ?_⟩
  · intro F K hF hK c d
    exact hG.2.2.1 F K (r11b_sourceMember_of_le hab h₀ hF)
      (r11b_sourceMember_of_le hab h₀ hK) c d
  · obtain ⟨C, hC, hbound⟩ := hG.2.2.2
    refine ⟨C, hC, fun F hF => ?_⟩
    obtain ⟨aL, hU, hnorm⟩ := hbound F (r11b_sourceMember_of_le hab h₀ hF)
    refine ⟨aL, r11b_outputRealization_of_le hab h₁ hU, ?_⟩
    calc outputNormSquare D γ M₁' aL (G F)
        ≤ outputNormSquare D γ M₁ aL (G F) :=
          r11b_outputNormSquare_antitone hab h₁ hU
      _ ≤ C ^ 2 * sourceNormSquare D γ M₀ F := hnorm
      _ ≤ C ^ 2 * sourceNormSquare D γ M₀' F :=
          mul_le_mul_of_nonneg_left (r11b_sourceNormSquare_mono hab h₀ hF) (sq_nonneg C)

end ContinuousFlexibility.Radial
