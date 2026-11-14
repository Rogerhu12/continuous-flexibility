module

public import ContinuousFlexibility.Analysis.N01aPartitionReference
public import ContinuousFlexibility.Analysis.N01aReferenceEigenfieldGraph
public import ContinuousFlexibility.Analysis.N01aReferenceWeightedMode
public import ContinuousFlexibility.Analysis.N01aReferenceSourceMeasurability

/-!
# A full radial reference with linearly growing cell indices

The pure-row inverse identifies the actual eigenfield and places it in the
weighted graph. Green reciprocity then recovers signed source
measurability. Thus the cell grouping retains the entire frozen R12
specification, including closed graph and smooth-core closure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory

theorem n01a_source_aemeasurable_of_reference_properties {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hpart : RadialPartition D)
    (hN : RadialNaturalKernels D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {G : RadialSource → RadialUnknown} (hγ : 0 < γ)
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hCore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    (hGreen : ReferenceGreenReciprocity D γ M₀ M₁) :
    ∀ F : RadialSource, SourceMember D γ M₀ F →
      AEMeasurable F.1 (radialPhysicalMeasure D) := by
  have hgraph := hG.1 ((0 : PolarPoint → ℝ), 1) (sourceMember_pure_row D γ M₀ 1)
  have houtput := referenceGraph_pure_row_eigenfield_output
    hgeom hpart hN hB hγ hCore hgraph
  exact n01a_source_aemeasurable_of_reference_phi_graph hgeom hN hG hGreen
    (referenceGraph_reference_eigenfield hgeom hN hB houtput)

theorem exists_n01a_grouped_reference {D : ReferenceData} (hD : IsRadialReference D) :
    ∃ E : RadialReference, ∃ σ : ℕ → ℕ,
      N01aReferenceCoarsening D E.val σ ∧ ∀ j, j ≤ 2 * E.val.cellIndex j + 1 := by
  apply exists_n01a_grouped_reference_of_source_measurable hD
  intro γ M₀ M₁ G hγ hG hCore hGreen
  exact n01a_source_aemeasurable_of_reference_properties hD.1.choose_spec.1
    hD.1.choose_spec.2.1 hD.2.1 hD.2.2.2.1 hγ hG hCore hGreen

end ContinuousFlexibility.Statements
