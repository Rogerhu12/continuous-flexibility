import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketPower
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

/-- A fixed base and angular loss control the literal sector packet
through every future parameter and angular order. -/
theorem n04PositiveGeometry_rootPacketSector_finiteShift_power
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (N requestedBase : ℕ) :
    ∃ B loss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C0 A : ℝ, 1 ≤ C0 ∧ 0 ≤ A ∧
      ∀ i : Fin 6, ∀ a d : ℕ, a + d ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ r ∈ radialCore D, ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative a (b + d) (fun p =>
          n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z) p i) (r, θ)),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ v : Fin k → (StateDirections S × ℝ),
      (∀ j, pairGrading (sectorGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → pairGrading (sectorGrading S) realGrading (s + loss) z ≤ R →
      (∀ j, pairGrading (sectorGrading S) realGrading (s + loss) (v j) ≤ R) →
        |J.D k z v| ≤ C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  obtain ⟨B, loss, hB, hb⟩ := n04PositiveGeometry_rootPacket_finiteShift_power
    hD hT hS hE C.referenceState N requestedBase
  refine ⟨B, loss, hB, fun K s => ?_⟩
  obtain ⟨C0, A, hC0, hA, hbound⟩ := hb K s
  refine ⟨C0, A, hC0, hA, ?_⟩
  intro i a d had b hbs r hr θ J k hk z hz hzlow v hv R hR hzR hvR
  let JP := n04PositiveGeometry_rootPacketMixed_parameter
    (C := C) (base := base) hD hT hS hε hr i a (b + d) θ
  let JQ := n04PositiveGeometry_rootPacketSectorMixed_parameter
    (C := C) (base := base) hD hT hS hε hr i a (b + d) θ
  have he : J.D k z v = JP.D k (liftSectorParameter S C z)
      (fun j => sectorParameterInclusion S (v j)) := by
    apply (congrArg (fun A : (StateDirections S × ℝ) [×k]→L[ℝ] ℝ => A v)
      (J.unique JQ k z hz)).trans
    change JP.D k ((C.referenceState, 0) + sectorParameterInclusion S z)
      (fun j => sectorParameterInclusion S (v j)) = _
    exact congrArg (fun y : AnnularState S × ℝ =>
      JP.D k y (fun j => sectorParameterInclusion S (v j)))
      (liftSectorParameter_eq_affine S C z).symm
  have hgrade (n : ℕ) :
      pairGrading (stateGrading S) realGrading n
        (liftSectorParameter S C z - (C.referenceState, 0)) =
      pairGrading (sectorGrading S) realGrading n z :=
    (congrArg (fun y : AnnularState S × ℝ => pairGrading (stateGrading S) realGrading n y)
      (liftSectorParameter_sub_reference S C z)).trans
        (pairGrading_sectorParameterInclusion S n z)
  have h := hbound i a d had b hbs (r, θ) ⟨hr, mem_univ _⟩
    (stateNeighborhood S C base ε) JP k hk (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl) (hz.2.le.trans hε)
    ((hgrade B).trans_le hzlow) (fun j => sectorParameterInclusion S (v j))
    (fun j => (pairGrading_sectorParameterInclusion S B (v j)).trans_le (hv j)) R hR
    ((hgrade (s + loss)).trans_le hzR)
    (fun j => (pairGrading_sectorParameterInclusion S (s + loss) (v j)).trans_le (hvR j))
  exact (congrArg abs he).trans_le h

end ContinuousFlexibility.Analysis
