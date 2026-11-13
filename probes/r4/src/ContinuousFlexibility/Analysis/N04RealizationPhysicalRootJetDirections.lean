import ContinuousFlexibility.Analysis.N04RealizationRootAbsorbedJoint
import ContinuousFlexibility.Analysis.N04RealizationJointSpatialEvaluation
import ContinuousFlexibility.Analysis.N06RootPhysicalSmallness
import ContinuousFlexibility.Analysis.SectorParameterGeometry
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Genuine state and angle jets of actual physical root coefficients

The normalized drift and speed kernel is composed only on its open
nondegenerate locus. The original N01 bounds place every actual root
point in that locus. Ordinary spatial jets are then restricted to that
same root, and the existing physical germ identifies the actual fields.
No parameter regularity of a chosen root-coordinate extension is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private def rootKernelDirections
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {f : X → N06RootNormalizedCoordinates}
    (J : SmoothDirections U f) :
    SmoothDirections
      (U ∩ f ⁻¹' {v | 0 < n06RootNormalizedQ v ∧
        0 < n06RootNormalizedDiscriminant v})
      (fun x => n06RootNormalizedFields (f x)) := by
  let V : Set N06RootNormalizedCoordinates :=
    {v | 0 < n06RootNormalizedQ v ∧ 0 < n06RootNormalizedDiscriminant v}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const n06RootNormalizedQ_contDiff.continuous).inter
      (isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous)
  have hW : IsOpen (U ∩ f ⁻¹' V) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.inter_mem (J.open_domain.mem_nhds hx.1)
      (((J.continuousOn x hx.1).continuousAt
        (J.open_domain.mem_nhds hx.1)).eventually (hV.mem_nhds hx.2))
  have hg : ContDiffOn ℝ ∞ n06RootNormalizedFields V := by
    intro v hv
    exact (n06RootNormalizedFields_contDiffAt hv.1.ne' hv.2).contDiffWithinAt
  exact (smoothDirectionsRestrict J hW (fun _ hx => hx.1)).comp_contDiff
    hV hg (fun _ hx => hx.2)

/-- Every evaluated ordinary spatial jet of either actual root field is
a genuine joint state-angle function, on the original sector neighborhood. -/
def n04Realization_physicalRootJet_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (hε : ε ≤ 1) (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (π : PolarPoint →L[ℝ] ℝ) (n : ℕ) (v : Fin n → PolarPoint) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z : (StateDirections S × ℝ) × ℝ =>
        iteratedFDeriv ℝ n
          (fun p => π (n06PhysicalRootFields D S C
            (liftSectorParameter S C z.1) p)) (r, z.2) v) := by
  let f : ((AnnularState S × ℝ) × PolarPoint) → N06RootNormalizedCoordinates :=
    fun z => n06ActualRootAbsorbedCoordinates D S z.1 z.2
  let U : Set ((AnnularState S × ℝ) × PolarPoint) :=
    stateNeighborhood S C base ε ×ˢ annularOpen D
  let W : Set ((AnnularState S × ℝ) × PolarPoint) :=
    U ∩ f ⁻¹' {u | 0 < n06RootNormalizedQ u ∧
      0 < n06RootNormalizedDiscriminant u}
  let JP : SmoothDirections U f :=
    n04Realization_rootAbsorbedCoordinates_joint hN.1.1 hT hS hε
  let JK : SmoothDirections W (fun z => n06RootNormalizedFields (f z)) :=
    rootKernelDirections JP
  let JS : SmoothDirections W (fun z => π (n06RootNormalizedFields (f z))) :=
    (smoothDirections_postcompCLM JK π).congr (fun _ _ => Function.comp_apply)
  let Jn := n04Realization_jointSpatialJet_directions JS n v
  let Z : Set ((StateDirections S × ℝ) × ℝ) :=
    sectorNeighborhood S base ε ε ×ˢ univ
  let c : (AnnularState S × ℝ) × PolarPoint := ((C.referenceState, 0), (r, 0))
  let L : ((StateDirections S × ℝ) × ℝ) →L[ℝ]
      ((AnnularState S × ℝ) × PolarPoint) :=
    ((sectorParameterInclusion S).comp
      (ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ℝ)).prod
      ((0 : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ).prod
        (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ))
  have hpoint (z : (StateDirections S × ℝ) × ℝ) :
      c + L z = (liftSectorParameter S C z.1, (r, z.2)) := by
    simp only [c, L, liftSectorParameter_eq_affine, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.zero_apply, Prod.mk_add_mk, add_zero, zero_add]
  have hZ : IsOpen Z := (isOpen_sectorNeighborhood S base ε ε).prod isOpen_univ
  have hmap : MapsTo (fun z => c + L z) Z W := by
    intro z hz
    change c + L z ∈ W
    simp only [hpoint]
    have hz' : liftSectorParameter S C z.1 ∈ stateNeighborhood S C base ε :=
      liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl
    have hd := n06_actualRootNormalized_denominators_lower hT hS hN hz'
      (hN.2.2.1.liftSectorParameter_sector z.1) hr hroot z.2
    have he := n06_absorbRoot_denominators
      (n06ActualRootNormalizedCoordinates D S (liftSectorParameter S C z.1) (r, z.2))
    refine ⟨⟨hz', hr, mem_univ _⟩, ?_, ?_⟩
    · change 0 < n06RootNormalizedQ
        (n06AbsorbRootParameter
          (n06ActualRootNormalizedCoordinates D S (liftSectorParameter S C z.1) (r, z.2)))
      rw [he.1]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hd.1
    · change 0 < n06RootNormalizedDiscriminant
        (n06AbsorbRootParameter
          (n06ActualRootNormalizedCoordinates D S (liftSectorParameter S C z.1) (r, z.2)))
      rw [he.2]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hd.2
  sorry

end ContinuousFlexibility.Analysis
