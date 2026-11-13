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
  sorry

end ContinuousFlexibility.Analysis
