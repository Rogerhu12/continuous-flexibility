import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketDirections
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Actual packet jets in the original sector parameters

The affine state inclusion has exactly the sector grading. Pulling back
the original packet towers therefore keeps the same base, angular loss,
material exponent and normalized directional estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositivePacketSectorStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε r : ℝ}

/-- The literal sector radial traces of all six actual coordinates. -/
def n04PositiveGeometry_rootPacketSectorTrace_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => radialBoundaryJet
        (fun p => n06ActualRootAbsorbedCoordinates D S
          (liftSectorParameter S C z.1) p i) r a z.2) := by
  let J := n04PositiveGeometry_rootPacketTrace_joint
    (C := C) (base := base) hD hT hS hε hr i a
  let L := (sectorParameterInclusion S).prodMap (ContinuousLinearMap.id ℝ ℝ)
  let c : (AnnularState S × ℝ) × ℝ := ((C.referenceState, 0), 0)
  have hpoint (z : (StateDirections S × ℝ) × ℝ) :
      c + L z = (liftSectorParameter S C z.1, z.2) := by
    apply Prod.ext
    · exact (liftSectorParameter_eq_affine S C z.1).symm
    · exact zero_add z.2
  have hmap : MapsTo (fun z => c + L z)
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (stateNeighborhood S C base ε ×ˢ univ) := by
    intro z hz
    change c + L z ∈ stateNeighborhood S C base ε ×ˢ univ
    rw [hpoint]
    exact ⟨liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl, mem_univ _⟩
  exact (J.compAffine L c ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    hmap).congr (fun z _ => congrArg
      (fun y : (AnnularState S × ℝ) × ℝ => radialBoundaryJet
        (fun p => n06ActualRootAbsorbedCoordinates D S y.1 p i) r a y.2) (hpoint z))

/-- The affine pullback of the actual spatial mixed jet. -/
def n04PositiveGeometry_rootPacketSectorMixed_parameter
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative a b (fun p =>
        n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z) p i) (r, θ)) := by
  let J := n04PositiveGeometry_rootPacketMixed_parameter
    (C := C) (base := base) hD hT hS hε hr i a b θ
  have hmap : MapsTo (fun z => (C.referenceState, 0) + sectorParameterInclusion S z)
      (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
    intro z hz
    exact (liftSectorParameter_eq_affine S C z) ▸
      liftSectorParameter_mem_stateNeighborhood hz le_rfl
  exact (J.compAffine (sectorParameterInclusion S) (C.referenceState, 0)
    (sectorNeighborhood_isOpen S base ε ε) hmap).congr (fun z _ =>
      congrArg (fun y : AnnularState S × ℝ => mixedDerivative a b
        (fun p => n06ActualRootAbsorbedCoordinates D S y p i) (r, θ))
        (liftSectorParameter_eq_affine S C z).symm)

/-- The finite intrinsic angular prolongation still has the original
joint sector and angle tower. -/
def n04PositiveGeometry_rootPacketSectorMixed_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a d : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => mixedDerivative a d (fun p => n06ActualRootAbsorbedCoordinates D S
        (liftSectorParameter S C z.1) p i) (r, z.2)) := by
  let J := n04PositiveGeometry_rootPacketSectorTrace_joint
    (C := C) (base := base) hD hT hS hε hr i a
  apply (smoothDirections_angularIterate J d).congr
  intro z _
  exact iteratedDeriv_radialBoundaryJet_eq_mixedDerivative isOpen_univ
    (((contDiff_apply ℝ ℝ i).comp
      (n06_actualRootAbsorbedCoordinates_contDiff hD hT hS
        (liftSectorParameter S C z.1))).contDiffOn)
    r (fun _ => mem_univ _) a d z.2

end ContinuousFlexibility.Analysis
