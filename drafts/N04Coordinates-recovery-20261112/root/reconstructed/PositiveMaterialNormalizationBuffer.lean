import ContinuousFlexibility.Analysis.PositiveMaterialExitChoice
import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer
import ContinuousFlexibility.Analysis.N01NormalizationRootSeparation

/-!
# Material caps that retain the actual normalization support

The existing normalization buffer is narrowed only at its outer exits.
Its inner normalization interval is unchanged.  Thus the same reference
column remains covered while both endpoint collars satisfy the ambient
distance caps used by material transport.  All choices precede the state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

def N04PositiveNormalizationBuffer.materialCapped
    {D : ReferenceData} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) K)
    (hf : Continuous (deriv D.w)) :
    N04PositiveNormalizationBuffer D.a D.b (deriv D.w) K where
  centerLeft := fun i => min (B.centerLeft i)
    (positiveMaterialLeftExit D (n04PositiveLeft i) (n04PositiveRight i))
  normalizationLeft := B.normalizationLeft
  normalizationRight := B.normalizationRight
  centerRight := fun i => max (B.centerRight i)
    (positiveMaterialRightExit D (n04PositiveLeft i) (n04PositiveRight i))
  ordered := by
    intro i
    have hb := n04PositiveComponent_bounds hf i
    have hm := positiveMaterialExits_spec hb.1 hb.2.1 hb.2.2
    have ho := B.ordered i
    exact ⟨lt_min ho.1 hm.1,
      lt_of_le_of_lt (min_le_left _ _) ho.2.1, ho.2.2.1,
      lt_of_lt_of_le ho.2.2.2.1 (le_max_left _ _),
      max_lt ho.2.2.2.2 hm.2.2.1⟩
  support := B.support

theorem N04PositiveNormalizationBuffer.materialCapped_region
    {D : ReferenceData} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) K)
    (hf : Continuous (deriv D.w)) :
    (B.materialCapped hf).region = B.region := rfl

theorem N04PositiveNormalizationBuffer.materialCapped_endpoint_caps
    {D : ReferenceData} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) K)
    (hf : Continuous (deriv D.w)) (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    (n04PositiveLeft i ≠ D.a →
      (B.materialCapped hf).centerLeft i - n04PositiveLeft i ≤
        Statements.endpointDistance D (n04PositiveLeft i) / 2) ∧
    (n04PositiveRight i ≠ D.b →
      n04PositiveRight i - (B.materialCapped hf).centerRight i ≤
        Statements.endpointDistance D (n04PositiveRight i) / 2) := by
  have hb := n04PositiveComponent_bounds hf i
  have hm := positiveMaterialExits_spec hb.1 hb.2.1 hb.2.2
  constructor
  · intro hl
    exact (sub_le_sub_right (min_le_right _ _) _).trans (hm.2.2.2.1 hl)
  · intro hr
    exact (sub_le_sub_left (le_max_right _ _) _).trans (hm.2.2.2.2 hr)

/-- The support and both material caps belong to one reference-only
buffer, including components touching an ambient endpoint. -/
theorem exists_materialCapped_positiveNormalizationBuffer
    {D : ReferenceData} (hf : Continuous (deriv D.w)) (hborder : RadialTrueBorder D) :
    ∃ B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi),
      IsOpen B.region ∧ Function.support (referenceColumn D) ⊆ B.region ∧
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
        (n04PositiveLeft i ≠ D.a →
          B.centerLeft i - n04PositiveLeft i ≤
            Statements.endpointDistance D (n04PositiveLeft i) / 2) ∧
        (n04PositiveRight i ≠ D.b →
          n04PositiveRight i - B.centerRight i ≤
            Statements.endpointDistance D (n04PositiveRight i) / 2) := by
  have hsupport : tsupport D.chi ⊆ n04PositiveRegion D.a D.b (deriv D.w) :=
    hborder.2.2.1
  obtain ⟨B⟩ := n04PositiveNormalizationBuffer_nonempty hf hborder.2.1 hsupport
  let B' := B.materialCapped hf
  exact ⟨B', B'.region_isOpen,
    (support_referenceColumn_subset_tsupport_chi D).trans
      (B'.support_subset_region hsupport), B.materialCapped_endpoint_caps hf⟩

end ContinuousFlexibility.Analysis
