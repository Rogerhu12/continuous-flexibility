import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketPower
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPacketSectorDirections

/-!
# The normalized bounds of the original sector packet

The affine parameter transfer is proved over abstract vector spaces.
Its specialization does not unfold the underlying physical jet tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositivePacketSectorPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem packet_affine_jet_apply
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {U : Set E} {V : Set F} {f : F → ℝ} {g : E → ℝ}
    (JP : SmoothDirections V f) (J : SmoothDirections U g)
    (L : E →L[ℝ] F) (c : F)
    (hmap : MapsTo (fun y => c + L y) U V)
    (heq : ∀ y ∈ U, f (c + L y) = g y)
    (k : ℕ) (z : E) (hz : z ∈ U) (v : Fin k → E) :
    J.D k z v = JP.D k (c + L z) (fun j => L (v j)) := by
  let JQ := (JP.compAffine L c J.open_domain hmap).congr heq
  have he := congrArg (fun A : E [×k]→L[ℝ] ℝ => A v) (J.unique JQ k z hz)
  exact he.trans (JP.compAffine_apply L c J.open_domain hmap k z v)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε r : ℝ}

set_option diagnostics true in
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
  let hprefix := n04PositiveGeometry_rootPacket_finiteShift_power
    hD hT hS hE C.referenceState N requestedBase
  let B : ℕ := hprefix.choose
  let loss : ℕ := hprefix.choose_spec.choose
  have hB := hprefix.choose_spec.choose_spec.1
  have hb := hprefix.choose_spec.choose_spec.2
  refine ⟨B, loss, hB, fun K s => ?_⟩
  let hcost := hb K s
  let C0 : ℝ := hcost.choose
  let A : ℝ := hcost.choose_spec.choose
  have hC0 := hcost.choose_spec.choose_spec.1
  have hA := hcost.choose_spec.choose_spec.2.1
  have hbound := hcost.choose_spec.choose_spec.2.2
  refine ⟨C0, A, hC0, hA, ?_⟩
  intro i a d had b hbs r hr θ J k hk z hz hzlow v hv R hR hzR hvR
  let JP := n04PositiveGeometry_rootPacketMixed_parameter
    (C := C) (base := base) hD hT hS hε hr i a (b + d) θ
  have hmap : MapsTo (fun y => (C.referenceState, 0) + sectorParameterInclusion S y)
      (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
    intro y hy
    exact (liftSectorParameter_eq_affine S C y) ▸
      liftSectorParameter_mem_stateNeighborhood hy le_rfl
  have he : J.D k z v = JP.D k (liftSectorParameter S C z)
      (fun j => sectorParameterInclusion S (v j)) := by
    have heq (y : StateDirections S × ℝ) (_hy : y ∈ sectorNeighborhood S base ε ε) :
        mixedDerivative a (b + d) (fun p => n06ActualRootAbsorbedCoordinates D S
          ((C.referenceState, 0) + sectorParameterInclusion S y) p i) (r, θ) =
        mixedDerivative a (b + d) (fun p => n06ActualRootAbsorbedCoordinates D S
          (liftSectorParameter S C y) p i) (r, θ) :=
      congrArg (fun x : AnnularState S × ℝ => mixedDerivative a (b + d)
        (fun p => n06ActualRootAbsorbedCoordinates D S x p i) (r, θ))
        (liftSectorParameter_eq_affine S C y).symm
    exact (packet_affine_jet_apply JP J (sectorParameterInclusion S)
      (C.referenceState, 0) hmap heq k z hz v).trans
        (congrArg (fun y : AnnularState S × ℝ =>
          JP.D k y (fun j => sectorParameterInclusion S (v j)))
          (liftSectorParameter_eq_affine S C z).symm)
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
