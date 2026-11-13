import ContinuousFlexibility.Analysis.N04bActualAtlasGeometry
import ContinuousFlexibility.Analysis.CanonicalStripGeometry

/-!
# Current negative fields on the fixed reference half

The physical unit point uses the fixed reference half, whereas the current
artificial cut may move.  The actual stored negative chart and height have
their prescribed physical germs throughout the whole original component.
Those germs therefore give the spatial regularity and symmetries needed
on the fixed reference half without identifying it with the moving domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D) (k m : ℕ) (side : Bool)
  (hi : e k = .inl (m, side))

include hi

/-- The fixed reference half is contained in its original negative
component, independently of the current state and its moving cut. -/
theorem n04NegativeGeometry_referenceHalf_subset_component :
    referencePhysicalPieceOpen S (n04bActualTypedAtlas hT hS hN hfield e) k ⊆
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA := n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hf := n04bTypedAtlasData_negative_fields
    (C := C) (L := L) (z := (C.referenceState, 0)) e
    (n04bActualNegativeChart hT hS hN hfield)
    (n04bActualNegativeHeight hT hS hN hfield)
    (n04bActualNegativeInverse hT hS hN hfield)
    (n04bActualReferenceCut hN) k m side hi
  intro p hp
  apply n04b_actualNegativeDomain_subset_component C L (C.referenceState, 0) m side
  exact hf.1 ▸ ((hA.referenceDomain k).symm ▸ hp)

/-- Actual current regularity, nondegeneracy and translation identities
on the fixed reference half.  The inverse lives on the fixed canonical
interval supplied by the original geometry. -/
theorem n04NegativeGeometry_referenceHalf_fields
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ContDiffOn ℝ ∞ (K.chart z k) (referencePhysicalPieceOpen S K k) ∧
      ContDiffOn ℝ ∞ (K.height z k) (referencePhysicalPieceOpen S K k) ∧
      (∀ p ∈ referencePhysicalPieceOpen S K k,
        planeJacobian (K.chart z k) p ≠ 0 ∧ 0 < K.height z k p) ∧
      (∀ p ∈ referencePhysicalPieceOpen S K k,
        K.chart z k (p + (0, Real.pi)) = K.chart z k p + (0, Real.pi) ∧
          K.height z k (p + (0, Real.pi)) = K.height z k p) ∧
      ContDiffOn ℝ ∞ (K.inverseChart z k) (canonicalOpen S K k) ∧
      (∀ p ∈ canonicalOpen S K k,
        K.inverseChart z k (p + (0, Real.pi)) = K.inverseChart z k p + (0, Real.pi)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hA := n04b_actualTypedAtlas_partA hT hS hN hfield e
  have H := n04bActualNegativeFunctions_spec hT hS hN hfield hz hs m side
  have hf := n04bTypedAtlasData_negative_fields
    (C := C) (L := L) (z := z) e
    (n04bActualNegativeChart hT hS hN hfield)
    (n04bActualNegativeHeight hT hS hN hfield)
    (n04bActualNegativeInverse hT hS hN hfield)
    (n04bActualReferenceCut hN) k m side hi
  have hsub := n04NegativeGeometry_referenceHalf_subset_component
    hT hS hN hfield e k m side hi
  have hFg (p : PolarPoint) (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
      K.chart z k =ᶠ[𝓝 p] n04bRootPhysicalChart
        (n04bActualTravelChart S C L z m) (C.travel m) side := by
    rw [hf.2.2.2.1]
    exact H.component_chart_germ hp
  have hHg (p : PolarPoint) (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
      K.height z k =ᶠ[𝓝 p] n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side := by
    rw [hf.2.2.2.2.2]
    exact H.component_height_germ hp
  have hregular (p : PolarPoint) (hp : p ∈ referencePhysicalPieceOpen S K k) :
      ContDiffAt ℝ ∞ (K.chart z k) p ∧ ContDiffAt ℝ ∞ (K.height z k) p ∧
        planeJacobian (K.chart z k) p ≠ 0 ∧ 0 < K.height z k p := by
    have hp' := hsub hp
    have hr := n04b_actualRootPhysical_regular_at hN hS hT hfield hz hs m side hp'
    refine ⟨hr.1.congr_of_eventuallyEq (hFg p hp'),
      hr.2.1.congr_of_eventuallyEq (hHg p hp'), ?_, ?_⟩
    · unfold planeJacobian
      rw [(hFg p hp').fderiv_eq]
      exact hr.2.2.1
    · rw [(hHg p hp').self_of_nhds]
      exact hr.2.2.2
  refine ⟨fun p hp => (hregular p hp).1.contDiffWithinAt,
    fun p hp => (hregular p hp).2.1.contDiffWithinAt,
    fun p hp => (hregular p hp).2.2, ?_,
    (hA.charts z hz hs k).2.2.2.2.2.1,
    fun p hp => canonicalInverse_periodic_on_open hA hz hs k hp⟩
  intro p hp
  have hp' := hsub hp
  have hshift : p + (0, Real.pi) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hp'.1, mem_univ _⟩
  constructor
  · rw [(hFg _ hshift).self_of_nhds, (hFg p hp').self_of_nhds]
    exact n04b_actualRootChart_period hN hS hT hfield hz hs m side
      ⟨hp'.1.1.le, hp'.1.2.le⟩
  · rw [(hHg _ hshift).self_of_nhds, (hHg p hp').self_of_nhds]
    exact n04b_actualRootHeight_period hN hS hT hfield hz hs m side hp'

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_referenceHalf_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_referenceHalf_fields
