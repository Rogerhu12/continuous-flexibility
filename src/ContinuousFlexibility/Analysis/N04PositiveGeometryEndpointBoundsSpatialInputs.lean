module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsSpatialKernel
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketSector
public import ContinuousFlexibility.Analysis.N06RootPhysicalSmallness

/-!
# Actual finite spatial inputs of the root kernel

All rows are literal mixed jets of the original absorbed packet at the
same root and angle. Their genuine joint towers use the original sector
parameters. N01 supplies the positive denominator locus, and a fixed
low parameter bound places every finite spatial tuple in one compact
ball independent of the root and all future angular orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04PositiveSpatialInputsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}

def n04PositiveGeometry_rootSpatialInput {n : ℕ} (c : OrderedFinpartition n)
    (w : Fin n → Fin 2) (r : ℝ) (z : (StateDirections S × ℝ) × ℝ) :
    N04RootRadialPacket c.length := fun ij =>
  mixedDerivative (n04PositiveGeometry_rootPartitionRadialOrder c w ij.1)
    (n04PositiveGeometry_rootPartitionAngularOrder c w ij.1)
    (fun p => n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z.1) p ij.2)
    (r, z.2)

theorem n04PositiveGeometry_rootSpatialInput_eq_packet
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {n : ℕ} (c : OrderedFinpartition n)
    (w : Fin n → Fin 2) (r : ℝ) (z : (StateDirections S × ℝ) × ℝ) :
    n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z =
      n04PositiveGeometry_rootSpatialPacket c
        (n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z.1))
        (r, z.2) (fun j => cylinderBasisVector (w j)) := by
  funext ij
  exact (n04PositiveGeometry_rootSpatialPacket_mixed c _
    (n06_actualRootAbsorbedCoordinates_contDiff hD hT hS
      (liftSectorParameter S C z.1)) (r, z.2) w ij).symm

theorem n04PositiveGeometry_rootSpatialInput_zero {n : ℕ} (c : OrderedFinpartition n)
    (w : Fin n → Fin 2) (r : ℝ) (z : (StateDirections S × ℝ) × ℝ) :
    (fun j => n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z (0, j)) =
      n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z.1) (r, z.2) := by
  funext j
  simp only [n04PositiveGeometry_rootSpatialInput, n04PositiveGeometry_rootPartitionRadialOrder,
    n04PositiveGeometry_rootPartitionAngularOrder, Fin.cons_zero, mixedDerivative,
    iteratedDeriv_zero]

def n04PositiveGeometry_rootSpatialInput_coordinateJoint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1) (hr : r ∈ radialCore D)
    {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2)
    (ij : Fin (c.length + 1) × Fin 6) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z ij) :=
  n04PositiveGeometry_rootPacketSectorMixed_joint hD hT hS hε hr ij.2
    (n04PositiveGeometry_rootPartitionRadialOrder c w ij.1)
    (n04PositiveGeometry_rootPartitionAngularOrder c w ij.1)

def n04PositiveGeometry_rootSpatialInput_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1) (hr : r ∈ radialCore D)
    {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r) :=
  smoothDirectionsScalarPi ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    (n04PositiveGeometry_rootSpatialInput_coordinateJoint hD hT hS hε hr c w)

theorem n04PositiveGeometry_rootSpatialInput_denominators
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2)
    {z : (StateDirections S × ℝ) × ℝ}
    (hz : z ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    (7 / 8 : ℝ) ≤ n06RootNormalizedQ
        (fun j => n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z (0, j)) ∧
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant
        (fun j => n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z (0, j)) := by
  have hb := n06_actualRootNormalized_denominators_lower hT hS hN
    (liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z.1) hr hroot z.2
  have he := n06_absorbRoot_denominators
    (n06ActualRootNormalizedCoordinates D S (liftSectorParameter S C z.1) (r, z.2))
  have hbound : (7 / 8 : ℝ) ≤ n06RootNormalizedQ
      (n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z.1) (r, z.2)) ∧
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant
      (n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z.1) (r, z.2)) :=
    ⟨hb.1.trans_eq he.1.symm, hb.2.trans_eq he.2.symm⟩
  simpa only [n04PositiveGeometry_rootSpatialInput_zero] using hbound

theorem n04PositiveGeometry_rootSpatialInput_mapsTo
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2) :
    MapsTo (n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r)
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootRadialKernelDomain c.length) := by
  intro z hz
  have hb := n04PositiveGeometry_rootSpatialInput_denominators hT hS hN hr hroot c w hz
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2⟩

/-- This compact-ball radius is fixed before any future parameter or
additional angular order and before the root/component is chosen. -/
theorem n04PositiveGeometry_rootSpatialInput_uniform_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ B : ℕ, N + 7 ≤ B →
      ∀ z : StateDirections S × ℝ, pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ r ∈ radialCore D, ∀ θ, ∀ n : ℕ, n ≤ N →
      ∀ c : OrderedFinpartition n, ∀ w : Fin n → Fin 2,
        ‖n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r (z, θ)‖ ≤ M := by
  let R0 := stateGrading S (N + 7) C.referenceState + 1
  let hdata := n06_actualRootAbsorbedCoordinates_spatial_bound hD hT hS N
    (show 0 ≤ R0 by dsimp only [R0]; positivity)
  let M : ℝ := hdata.choose
  have hM := hdata.choose_spec.1
  have hb := hdata.choose_spec.2
  refine ⟨M, hM, ?_⟩
  intro B hB z hz r hr θ n hn c w
  have hsmall := (sectorPairGrading_monotone S hB z).trans hz
  have hdir : stateGrading S (N + 7) z.1.val ≤ 1 :=
    (le_add_of_nonneg_right (apply_nonneg (realGrading (N + 7)) z.2)).trans hsmall
  have hq : |z.2| ≤ 1 :=
    (le_add_of_nonneg_left (apply_nonneg (sectorGrading S (N + 7)) z.1)).trans hsmall
  have hs : stateGrading S (N + 7) (liftSectorParameter S C z).1 ≤ R0 :=
    (map_add_le_add (stateGrading S (N + 7)) C.referenceState z.1.val).trans
      (add_le_add le_rfl hdir)
  rw [n04PositiveGeometry_rootSpatialInput_eq_packet hD hT hS]
  apply n04PositiveGeometry_rootSpatialPacket_norm_le c _ (r, θ) _ hM
  · intro j
    unfold cylinderBasisVector
    split <;> norm_num [Prod.norm_mk]
  · intro j hj
    exact hb (liftSectorParameter S C z) hs hq j (hj.trans hn) (r, θ) ⟨hr, mem_univ _⟩

end ContinuousFlexibility.Analysis
