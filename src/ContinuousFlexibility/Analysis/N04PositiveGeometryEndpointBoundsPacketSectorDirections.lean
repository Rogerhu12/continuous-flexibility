module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketDirections
public import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Actual packet jets in the original sector parameters

The affine state inclusion has exactly the sector grading. Pulling back
the original packet towers therefore keeps the same base, angular loss,
material exponent and normalized directional estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositivePacketSectorStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n04PositivePacketSectorParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul
local instance n04PositivePacketSectorRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

private def packet_affine_directions
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {U : Set E} {V : Set F} (u : E → F) (L : E →L[ℝ] F) (c : F)
    (hU : IsOpen U) (hmap : MapsTo u U V)
    (heq : ∀ y, u y = c + L y) {f : F → ℝ}
    (J : SmoothDirections V f) : SmoothDirections U (fun y => f (u y)) := by
  have hm : MapsTo (fun y => c + L y) U V := by
    intro y hy
    exact (congrArg (fun q : F => q ∈ V) (heq y)).mp (hmap hy)
  exact (J.compAffine L c hU hm).congrOn (fun y _ => congrArg f (heq y).symm)

private def packet_affine_angle_directions
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {U : Set E} {V : Set F} (u : E → F) (L : E →L[ℝ] F) (c : F)
    (hU : IsOpen U) (hmap : MapsTo u U V) (heq : ∀ y, u y = c + L y)
    {f : F × ℝ → ℝ} (J : SmoothDirections (V ×ˢ univ) f) :
    SmoothDirections (U ×ˢ univ) (fun y => f (u y.1, y.2)) := by
  apply packet_affine_directions (U := U ×ˢ (univ : Set ℝ))
    (V := V ×ˢ (univ : Set ℝ)) (f := f) (fun y : E × ℝ => (u y.1, y.2))
    (L.prodMap (ContinuousLinearMap.id ℝ ℝ)) (c, 0) (hU.prod isOpen_univ)
    (fun y hy => ⟨hmap hy.1, mem_univ _⟩) ?_ J
  intro y
  simpa only [ContinuousLinearMap.coe_prodMap', Prod.map_apply',
    ContinuousLinearMap.id_apply, Prod.mk_add_mk, zero_add] using
      congrArg (fun q : F => (q, y.2)) (heq y.1)

private def packet_angular_directions
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f g : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ univ) f) (d : ℕ)
    (heq : ∀ y ∈ U ×ˢ (univ : Set ℝ),
      iteratedDeriv d (fun θ => f (y.1, θ)) y.2 = g y) :
    SmoothDirections (U ×ˢ univ) g :=
  (smoothDirections_angularIterate J d).congrOn heq

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε r : ℝ}

set_option backward.isDefEq.respectTransparency false in
/-- The literal sector radial traces of all six actual coordinates. -/
def n04PositiveGeometry_rootPacketSectorTrace_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => radialBoundaryJet
        (fun p => n06ActualRootAbsorbedCoordinates D S
          (liftSectorParameter S C z.1) p i) r a z.2) :=
  packet_affine_angle_directions
    (f := fun y : (AnnularState S × ℝ) × ℝ => radialBoundaryJet
      (fun p => n06ActualRootAbsorbedCoordinates D S y.1 p i) r a y.2)
    (liftSectorParameter S C) (sectorParameterInclusion S)
    (C.referenceState, 0) (sectorNeighborhood_isOpen S base ε ε)
    (fun _ hz => liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (liftSectorParameter_eq_affine S C)
    (n04PositiveGeometry_rootPacketTrace_joint
      (C := C) (base := base) hD hT hS hε hr i a)

set_option backward.isDefEq.respectTransparency false in
/-- The affine pullback of the actual spatial mixed jet. -/
def n04PositiveGeometry_rootPacketSectorMixed_parameter
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative a b (fun p =>
        n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z) p i) (r, θ)) :=
  packet_affine_directions
    (f := fun y : AnnularState S × ℝ => mixedDerivative a b
      (fun p => n06ActualRootAbsorbedCoordinates D S y p i) (r, θ))
    (liftSectorParameter S C) (sectorParameterInclusion S)
    (C.referenceState, 0) (sectorNeighborhood_isOpen S base ε ε)
    (fun _ hz => liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (liftSectorParameter_eq_affine S C)
    (n04PositiveGeometry_rootPacketMixed_parameter
      (C := C) (base := base) hD hT hS hε hr i a b θ)

set_option backward.isDefEq.respectTransparency false in
/-- The finite intrinsic angular prolongation still has the original
joint sector and angle tower. -/
def n04PositiveGeometry_rootPacketSectorMixed_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a d : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => mixedDerivative a d (fun p => n06ActualRootAbsorbedCoordinates D S
        (liftSectorParameter S C z.1) p i) (r, z.2)) := by
  apply packet_angular_directions
    (n04PositiveGeometry_rootPacketSectorTrace_joint
      (C := C) (base := base) hD hT hS hε hr i a) d
  intro z _
  exact iteratedDeriv_radialBoundaryJet_eq_mixedDerivative isOpen_univ
    (((contDiff_apply ℝ ℝ i).comp
      (n06_actualRootAbsorbedCoordinates_contDiff hD hT hS
        (liftSectorParameter S C z.1))).contDiffOn)
    r (fun _ => mem_univ _) a d z.2

end ContinuousFlexibility.Analysis
