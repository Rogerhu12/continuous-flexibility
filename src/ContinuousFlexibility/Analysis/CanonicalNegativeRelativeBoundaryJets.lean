module

public import ContinuousFlexibility.Analysis.CanonicalNegativeRelativePrincipal
public import ContinuousFlexibility.Analysis.CanonicalActualEndpointFields
public import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
public import ContinuousFlexibility.Analysis.OpenGermBoundaryJets

/-!
# Reference principal jets at the true negative roots

The adjugate expression uses only the actual forward relative map and
height ratio.  It is ordinarily smooth at the closed physical endpoints.
The proved equation on the open negative half therefore determines every
finite ordinary boundary jet.  No equation across the root is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem canonicalCurrentRelativeAdjugate_contDiffAt_closed
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k : ℕ) (A : SymmetricCoefficients)
    {p : PolarPoint} (hp : p ∈ physicalPieceClosed S K (C.referenceState, 0) k)
    (ha : ContDiffAt ℝ ∞ A.a (canonicalCurrentPoint C K z k p))
    (hb : ContDiffAt ℝ ∞ A.b (canonicalCurrentPoint C K z k p))
    (hc : ContDiffAt ℝ ∞ A.c (canonicalCurrentPoint C K z k p)) :
    ContDiffAt ℝ ∞ (adjugateCoordinatePrincipalCoefficients A
      (canonicalCurrentPoint C K z k) (n04CoordinatesCurrentHeightRatio C K z k)).a p ∧
    ContDiffAt ℝ ∞ (adjugateCoordinatePrincipalCoefficients A
      (canonicalCurrentPoint C K z k) (n04CoordinatesCurrentHeightRatio C K z k)).b p ∧
    ContDiffAt ℝ ∞ (adjugateCoordinatePrincipalCoefficients A
      (canonicalCurrentPoint C K z k) (n04CoordinatesCurrentHeightRatio C K z k)).c p := by
  have hτ := n04Coordinates_currentPoint_contDiffAt_closed hA href hsref hz hs k hp
  have hq := n04Coordinates_currentHeightRatio_contDiffAt_pos_closed hA href hsref hz hs k hp
  have hinv := canonicalCurrentPoint_closed_inverse_data hA href hsref hz hs k hp
  have hprod := planeJacobian_inverse_mul_of_germ
    (hτ.differentiableAt (by simp)) (hinv.1.differentiableAt (by simp)) hinv.2.1
  have hJ : planeJacobian (canonicalCurrentPoint C K z k) p ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hprod
    exact zero_ne_one hprod
  exact contDiffAt_adjugateCoordinatePrincipalCoefficients
    (A := A) (F := canonicalCurrentPoint C K z k)
    (h := n04CoordinatesCurrentHeightRatio C K z k) ha hb hc hτ hq.1 hJ hq.2.ne'

private theorem typedNegative_closed_mem_annulus
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (Γ : ℕ → PolarPoint → PolarPoint)
    (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p ∈ closure (n04bTypedPhysicalDomain (D := D) C Γ (.inl (m, side)))) :
    p ∈ annularOpen D := by
  have hc := closure_mono (n04b_typed_negative_domain_subset
    (D := D) (C := C) (Γ := Γ) (m, side)) hp
  rw [closure_prod_eq, closure_Ioo (hC.1 m).2.1.ne, closure_univ] at hc
  exact ⟨⟨(hC.1 m).1.trans_le hc.1.1, hc.1.2.trans_lt (hC.1 m).2.2⟩, mem_univ _⟩

/-- Every closed-half ordinary jet of the actual relative adjugate field
is the corresponding jet of the reference physical coefficient. -/
theorem n04Coordinates_actualAtlas_relativeAdjugate_closed_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S (n04bActualTypedAtlas hT hS hN hfield e)
      (C.referenceState, 0) k) (i : Fin 3) (n : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    iteratedFDeriv ℝ n
      (canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients
        (L.coefficients z) (canonicalCurrentPoint C K z k)
        (n04CoordinatesCurrentHeightRatio C K z k))) p =
      iteratedFDeriv ℝ n
        (canonicalCoefficientComponent i (L.coefficients (C.referenceState, 0))) p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let B := adjugateCoordinatePrincipalCoefficients (L.coefficients z)
    (canonicalCurrentPoint C K z k) (n04CoordinatesCurrentHeightRatio C K z k)
  have hA : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref := hN.1.1.2.2.1.stateSector
  have hcore (w : AnnularState S × ℝ) {q : PolarPoint}
      (hq : q ∈ physicalPieceClosed S K w k) : q ∈ annularOpen D := by
    apply typedNegative_closed_mem_annulus hN.1.1.2.2.2.1
      (n04bActualTravelChart S C L w) m side
    simpa only [physicalPieceClosed, K, n04bActualTypedAtlas,
      n04bTypedAtlasData_physicalPieceOpen, hi] using hq
  have hpD := hcore (C.referenceState, 0) hp
  have hx := n04Coordinates_currentPoint_mapsTo_closed hA href hsref hz hs k hp
  have hxD := hcore z hx
  have hreg₀ := hfield.smooth_coefficients (C.referenceState, 0) href hsref
  have hreg₁ := hfield.smooth_coefficients z hz hs
  have hnhds₀ := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpD
  have hnhds₁ := (isOpen_Ioo.prod isOpen_univ).mem_nhds hxD
  have hB := canonicalCurrentRelativeAdjugate_contDiffAt_closed hA href hsref hz hs k
    (L.coefficients z) hp (hreg₁.1.contDiffAt hnhds₁)
    (hreg₁.2.1.contDiffAt hnhds₁) (hreg₁.2.2.contDiffAt hnhds₁)
  have hBi : ContDiffAt ℝ ∞ (canonicalCoefficientComponent i B) p := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hB.1
    · exact hB.2.1
    · exact hB.2.2
  have hAi : ContDiffAt ℝ ∞
      (canonicalCoefficientComponent i (L.coefficients (C.referenceState, 0))) p := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hreg₀.1.contDiffAt hnhds₀
    · exact hreg₀.2.1.contDiffAt hnhds₀
    · exact hreg₀.2.2.contDiffAt hnhds₀
  have he : EqOn (canonicalCoefficientComponent i B)
      (canonicalCoefficientComponent i (L.coefficients (C.referenceState, 0)))
      (physicalPieceOpen S K (C.referenceState, 0) k) := by
    intro q hq
    have hclosed : q ∈ physicalPieceClosed S K (C.referenceState, 0) k := subset_closure hq
    have hτ := n04Coordinates_currentPoint_contDiffAt_closed hA href hsref hz hs k hclosed
    have hqpos := n04Coordinates_currentHeightRatio_contDiffAt_pos_closed
      hA href hsref hz hs k hclosed
    have hinv := canonicalCurrentPoint_closed_inverse_data hA href hsref hz hs k hclosed
    have hr := reverseCoordinatePrincipalCoefficients_eq_adjugate (L.coefficients z)
      (F := canonicalCurrentPoint C K z k) (G := canonicalReferencePoint C K z k)
      (h := n04CoordinatesCurrentHeightRatio C K z k) (x := q)
      (hτ.differentiableAt (by simp)) (hinv.1.differentiableAt (by simp))
      hinv.2.1 hqpos.2.ne'
    have hn := n04Coordinates_actualAtlas_relativePrincipal_on_negative
      hT hS hN hfield e hz hs k m side hi q hq
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hr.1.symm.trans hn.1
    · exact hr.2.1.symm.trans hn.2.1
    · exact hr.2.2.symm.trans hn.2.2
  exact iteratedFDeriv_eq_of_eqOn_open_of_mem_closure
    (hA.domains _ href hsref k).1 hp he hBi hAi n

/-- The same conclusion at either true component root, with the actual
paired atlas index and no additional boundary equation. -/
theorem n04Coordinates_actualAtlas_relativeAdjugate_root_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) (i : Fin 3) (n : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let k := if side then (K.cutPair m).2 else (K.cutPair m).1
    let c := if side then C.right m else C.left m
    iteratedFDeriv ℝ n
      (canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients
        (L.coefficients z) (canonicalCurrentPoint C K z k)
        (n04CoordinatesCurrentHeightRatio C K z k))) (c, θ) =
      iteratedFDeriv ℝ n
        (canonicalCoefficientComponent i (L.coefficients (C.referenceState, 0))) (c, θ) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hA := n04b_actualTypedAtlas_partA hT hS hN hfield e
  have hcut := n04bActualTypedAtlas_cutGeometry hT hS hN hfield e
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref := hN.1.1.2.2.1.stateSector
  have hi : e k = .inl (m, side) := by
    have hpair : K.cutPair m = (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl
    change e (if side then (K.cutPair m).2 else (K.cutPair m).1) = _
    rw [hpair]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Equiv.apply_symm_apply]
  have hp := (canonicalCutRoot_mem_closed_and_zero hA hcut href hsref m side θ).1
  exact n04Coordinates_actualAtlas_relativeAdjugate_closed_jets
    hT hS hN hfield e hz hs k m side hi hp i n

end ContinuousFlexibility.Analysis
