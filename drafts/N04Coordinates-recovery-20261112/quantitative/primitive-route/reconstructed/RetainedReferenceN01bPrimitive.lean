import ContinuousFlexibility.Analysis.RetainedReferenceN01aPrimitive
import ContinuousFlexibility.Analysis.NeighborhoodFlowRetainedGeometry

/-!
# Retained primitive geometry through the actual N01b construction

The same retained reference supplies the controls and the common actual
flow neighborhood. Whole-component hosts, the border support and the
uniform optical lower bound survive because flow installation leaves
the reference, cells, controls and endpoints unchanged. No N01c or N02/N03
certificate is assumed or transferred to a different witness.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- The actual retained N01a factory and the relative flow construction
produce one N01b witness carrying the genuine primitive input. -/
theorem retainedReference_exists_n01b_primitive_geometry
    {S₀ : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K q length) (hS₀ : IsSelectedTail S₀)
    (hstart : 100 ≤ S₀.chain.index)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (hD : IsRadialReference Γ.reference)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces Γ.reference T S)
    (hphi : HeightMember Γ.reference T referenceBeta
      (fun p : PolarPoint => Γ.reference.phi p.1 * cosineMode 2 p.2)) :
    ∃ C : NonlinearGeometryData S, ∃ ε : ℝ,
      IsMaterialData Γ.reference (enlargedMaterialData T) ∧
      IsPhysicalSpaces Γ.reference (enlargedMaterialData T) S ∧
      Blueprint.N01PartA Γ.reference (enlargedMaterialData T) S C ∧
      0 < ε ∧ Blueprint.N01PartB Γ.reference S C 4 ε ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m)) ∧
      tsupport Γ.reference.chi ⊆ Ioo Γ.reference.a Γ.reference.b ∧
      ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
        B⁻¹ * (enlargedMaterialData T).E0 ((enlargedMaterialData T).sample (C.cell m)) ^ (-B) *
            min (r - C.left m) (C.right m - r) ≤
          -deriv Γ.reference.w r / (r * Γ.reference.w r) := by
  obtain ⟨C, hT', hS', hA, hhost, hchi, B, hB, hlower⟩ :=
    retainedReference_exists_n01a_primitive_geometry
      P hS₀ hstart hband hq hΓ hw hcoordinates hD hT hS hphi
  obtain ⟨Θ, ε, hε, hPartB⟩ := Blueprint.exists_n01b_circleFlowGeometry hT' hS' hA
  exact ⟨circleFlowGeometry C Θ, ε, hT', hS', circleFlowGeometry_partA hA Θ,
    hε, hPartB, hhost, hchi, B, hB, hlower⟩

end ContinuousFlexibility.Radial
