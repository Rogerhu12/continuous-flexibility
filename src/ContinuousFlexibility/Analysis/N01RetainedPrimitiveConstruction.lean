module

public import ContinuousFlexibility.Analysis.N01ActualRetainedReference
public import ContinuousFlexibility.Analysis.N01aFixedReferencePrimitiveContext
public import ContinuousFlexibility.Analysis.NeighborhoodFlowRetainedGeometry
public import ContinuousFlexibility.Analysis.N01PrimitiveFixedWitnessConstruction
public import ContinuousFlexibility.Analysis.N01cActualPrimitiveGeometry
public import ContinuousFlexibility.Analysis.N01cRetainedComponentEnumeration

/-!
# N01 on the actual retained reference

The completed reference, its retained coordinates and its primitive
optical geometry are carried through the actual material, space, control
and flow constructions. Only the three flow fields are installed in the
control geometry. The N01c conclusion is the parameter-order-loss
contract of the selected upstream version.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem n01c_exists_retained_primitive_properties :
    ∃ S₀ : SelectedTailData, ∃ K : SeedCentralCutoff,
      ∃ Cstar : ℝ, ∃ requested : ℕ, ∃ length : ℝ,
      ∃ metadata : R10aSelectedMetadata Cstar requested S₀,
      ∃ P : SeedRetainedPair S₀ K 1 length, ∃ Γ : ConnectedReferenceGeometry,
        4096 ≤ S₀.chain.index ∧ Γ.Realizes ∧
        Γ.reference.w = P.pair.profile ∧
        RadialConstructionGeometry Γ.reference ∧
        R11aRetainedCoordinates P Γ ∧ IsRadialReference Γ.reference ∧
        ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
          ∃ C : NonlinearGeometryData S, ∃ base loss : ℕ, ∃ ε : ℝ,
            IsMaterialData Γ.reference T ∧ IsPhysicalSpaces Γ.reference T S ∧
            N01Properties Γ.reference T S C base loss ε ∧
            N01PrimitiveGeometry Γ.reference T S C ∧
            (∀ r ∈ Ioo Γ.reference.a Γ.reference.b, 1 ≤ T.E0 r) := by
  obtain ⟨S₀, K, Cstar, requested, length, metadata, P, Γ,
    hindex, hΓ, hw, hconstruction, hcoordinates, hD⟩ :=
    n01c_exists_actual_retained_reference
  have hprimitive : N01RadialPrimitiveGeometry Γ.reference :=
    P.n01c_radialPrimitiveGeometry Γ metadata.selected metadata.first_two
      (by omega) zero_lt_one hΓ hw hconstruction hcoordinates
  let D : RadialReference := ⟨Γ.reference, hD⟩
  obtain ⟨T, S, C, hT, hS, hA, hG, hE⟩ :=
    n01a_exists_fixedReference_primitive_context D hprimitive
      (fun host hhost => P.n01c_component_enumeration metadata Γ
        zero_lt_one hΓ hw hcoordinates host hhost)
  obtain ⟨Θ, ε, hε, hB⟩ := exists_n01b_circleFlowGeometry hT hS hA
  have hA' : N01PartA Γ.reference T S (circleFlowGeometry C Θ) :=
    circleFlowGeometry_partA hA Θ
  have hG' : N01PrimitiveGeometry Γ.reference T S (circleFlowGeometry C Θ) := hG
  obtain ⟨base, loss, ε', _, _, _, hN, hG'⟩ :=
    n01Primitive_exists_fixedWitness_properties hS hT hA' hε hB hG' hE
  exact ⟨S₀, K, Cstar, requested, length, metadata, P, Γ,
    hindex, hΓ, hw, hconstruction, hcoordinates, hD,
    T, S, circleFlowGeometry C Θ, base, loss, ε', hT, hS, hN, hG', hE⟩

end ContinuousFlexibility.Radial
