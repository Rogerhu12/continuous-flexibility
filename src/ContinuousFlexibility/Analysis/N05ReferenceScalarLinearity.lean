import ContinuousFlexibility.Analysis.N05ReferenceLeftChoice
import ContinuousFlexibility.Radial.ReferenceCommonInverse
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Linearity of the single physical endpoint scalar

The selected left constant depends only on the actual physical equivalence
class whenever a positive-weight output realization exists. Its linearity
then follows from the literal output class and the fixed physical inverse,
without imposing pointwise linearity on representatives chosen by that inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

theorem n05_referenceLeftConstant_congr_ae
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U V : RadialUnknown}
    (hU : OutputMember D γ M U) (hV : OutputMember D γ M V)
    (hUV : RadialRepresentativeEq D U V) :
    n05_referenceLeftConstant D U = n05_referenceLeftConstant D V := by
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  have haV := OutputRealization.congr_ae hD.choose_spec.1.2.1.le ha hUV
    hb.2.2.1 hb.2.2.2
  rw [n05_referenceLeftConstant_eq hD hborder hγ ha,
    n05_referenceLeftConstant_eq hD hborder hγ hb]
  exact n05_outputRealization_leftConstant_unique hD hborder hγ hγ haV hb

theorem n05_referenceLeftConstant_linear_combination
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U V : RadialUnknown}
    (hU : OutputMember D γ M U) (hV : OutputMember D γ M V) (c d : ℝ) :
    n05_referenceLeftConstant D (c • U + d • V) =
      c * n05_referenceLeftConstant D U + d * n05_referenceLeftConstant D V := by
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  have hsum := OutputRealization.add hD.choose_spec.1.2.1.le
    (OutputRealization.smul ha c) (OutputRealization.smul hb d)
  rw [n05_referenceLeftConstant_eq hD hborder hγ hsum,
    n05_referenceLeftConstant_eq hD hborder hγ ha,
    n05_referenceLeftConstant_eq hD hborder hγ hb]

/-- The actual inverse has a linear endpoint scalar even though its
pointwise representatives are only required to be linear almost everywhere. -/
theorem n05_referenceInverse_leftConstant_linear_combination
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M0 M1 : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G)
    {F H : RadialSource} (hF : SourceMember D γ M0 F) (hH : SourceMember D γ M0 H)
    (c d : ℝ) :
    n05_referenceLeftConstant D (G (c • F + d • H)) =
      c * n05_referenceLeftConstant D (G F) + d * n05_referenceLeftConstant D (G H) := by
  have hab := hD.choose_spec.1.2.1.le
  have hsource := SourceMember.add hab hD.choose_spec.2.1
    (SourceMember.smul hF c) (SourceMember.smul hH d)
  have hUF := (hG.1 F hF).1
  have hUH := (hG.1 H hH).1
  have hsum := OutputMember.add hab (OutputMember.smul hUF c) (OutputMember.smul hUH d)
  exact (n05_referenceLeftConstant_congr_ae hD hborder hγ
    (hG.1 (c • F + d • H) hsource).1 hsum
    (hG.2.2.1 F H hF hH c d)).trans
      (n05_referenceLeftConstant_linear_combination hD hborder hγ hUF hUH c d)

end ContinuousFlexibility.Radial
