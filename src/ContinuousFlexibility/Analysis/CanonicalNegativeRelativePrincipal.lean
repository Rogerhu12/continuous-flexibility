import ContinuousFlexibility.Analysis.RelativePrincipalCoefficients
import ContinuousFlexibility.Analysis.ActualNegativePrincipalDensity
import ContinuousFlexibility.Analysis.CanonicalClosedTransport
import ContinuousFlexibility.Analysis.StateNeighborhood
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Actual negative reference-to-current principal transport

Both states are compared through their genuine stored charts.  The common
Airy density is supplied by the actual characteristic construction, not
by assuming PartB or the desired relative coefficient match.  One Bool
parameter covers both root-adjacent negative halves.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem canonicalRelativePrincipal_eq_of_negative_densities
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k : ℕ) (A₀ A₁ : SymmetricCoefficients)
    (hnormal₀ : ∀ p ∈ physicalPieceOpen S K (C.referenceState, 0) k,
      (coordinatePrincipalDensity A₀ (K.chart (C.referenceState, 0) k)
        (K.height (C.referenceState, 0) k)).a p = 1 ∧
      (coordinatePrincipalDensity A₀ (K.chart (C.referenceState, 0) k)
        (K.height (C.referenceState, 0) k)).b p = 0 ∧
      (coordinatePrincipalDensity A₀ (K.chart (C.referenceState, 0) k)
        (K.height (C.referenceState, 0) k)).c p =
          -(K.chart (C.referenceState, 0) k p).1)
    (hnormal₁ : ∀ p ∈ physicalPieceOpen S K z k,
      (coordinatePrincipalDensity A₁ (K.chart z k) (K.height z k)).a p = 1 ∧
      (coordinatePrincipalDensity A₁ (K.chart z k) (K.height z k)).b p = 0 ∧
      (coordinatePrincipalDensity A₁ (K.chart z k) (K.height z k)).c p =
        -(K.chart z k p).1)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K (C.referenceState, 0) k) :
    (reverseCoordinatePrincipalCoefficients A₁
      (canonicalCurrentPoint C K z k) (canonicalReferencePoint C K z k)
      (n04CoordinatesCurrentHeightRatio C K z k)).a p = A₀.a p ∧
    (reverseCoordinatePrincipalCoefficients A₁
      (canonicalCurrentPoint C K z k) (canonicalReferencePoint C K z k)
      (n04CoordinatesCurrentHeightRatio C K z k)).b p = A₀.b p ∧
    (reverseCoordinatePrincipalCoefficients A₁
      (canonicalCurrentPoint C K z k) (canonicalReferencePoint C K z k)
      (n04CoordinatesCurrentHeightRatio C K z k)).c p = A₀.c p := by
  let τ : PolarPoint → PolarPoint := canonicalCurrentPoint C K z k
  let σ : PolarPoint → PolarPoint := canonicalReferencePoint C K z k
  have hcharts₀ := hA.charts (C.referenceState, 0) href hsref k
  have hcharts₁ := hA.charts z hz hs k
  have hU₀ : IsOpen (physicalPieceOpen S K (C.referenceState, 0) k) :=
    (hA.domains (C.referenceState, 0) href hsref k).1
  have hU₁ : IsOpen (physicalPieceOpen S K z k) := (hA.domains z hz hs k).1
  have hV : IsOpen (canonicalOpen S K k) := isOpen_Ioo.prod isOpen_univ
  have hFp : K.chart (C.referenceState, 0) k p ∈ canonicalOpen S K k := hcharts₀.1 hp
  have hx : τ p ∈ physicalPieceOpen S K z k := hcharts₁.2.1 hFp
  have hFx : K.chart z k (τ p) = K.chart (C.referenceState, 0) k p :=
    hcharts₁.2.2.2.1 _ hFp
  have hτ : ContDiffAt ℝ ∞ τ p :=
    n04Coordinates_currentPoint_contDiffAt_closed hA href hsref hz hs k (subset_closure hp)
  have hF₁ : ContDiffAt ℝ ∞ (K.chart z k) (τ p) :=
    (hcharts₁.2.2.2.2.1 _ hx).contDiffAt (hU₁.mem_nhds hx)
  have hG₀ : ContDiffAt ℝ ∞ (K.inverseChart (C.referenceState, 0) k)
      (K.chart z k (τ p)) := by
    rw [hFx]
    exact (hcharts₀.2.2.2.2.2.1 _ hFp).contDiffAt (hV.mem_nhds hFp)
  have hσ : ContDiffAt ℝ ∞ σ (τ p) :=
    ContDiffAt.fun_comp (f := K.chart z k)
      (g := K.inverseChart (C.referenceState, 0) k) (τ p) hG₀ hF₁
  have hinverse : σ ∘ τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) :=
    n04Coordinates_referencePoint_currentPoint_germ hA href hsref hz hs k
      (subset_closure hp)
  have hchart : K.chart z k ∘ τ =ᶠ[𝓝 p] K.chart (C.referenceState, 0) k := by
    filter_upwards [hU₀.mem_nhds hp] with y hy
    exact hcharts₁.2.2.2.1 _ (hcharts₀.1 hy)
  have hp₀ := hcharts₀.2.2.2.2.2.2.2 p hp
  have hp₁ := hcharts₁.2.2.2.2.2.2.2 (τ p) hx
  have hd₀ := hnormal₀ p hp
  have hd₁ := hnormal₁ (τ p) hx
  exact reverseCoordinatePrincipalCoefficients_eq_of_common_density A₀ A₁
    canonicalAiryPrincipalCoefficients (K.chart (C.referenceState, 0) k)
    (K.chart z k) τ σ (K.height (C.referenceState, 0) k) (K.height z k) p
    (hτ.differentiableAt (by simp)) (hσ.differentiableAt (by simp))
    (hF₁.differentiableAt (by simp)) hinverse hchart hp₀.2.1 hp₁.2.1
    hp₀.1.ne' hp₁.1.ne'
    ⟨hd₀.1.symm, hd₀.2.1.symm, hd₀.2.2.symm⟩
    ⟨hd₁.1.symm, hd₁.2.1.symm, hd₁.2.2.symm⟩

/-- The relative principal field equals the reference physical field on
each actual negative half.  Every normal-form input is constructed here. -/
theorem n04Coordinates_actualAtlas_relativePrincipal_on_negative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∀ p ∈ physicalPieceOpen S K (C.referenceState, 0) k,
      (reverseCoordinatePrincipalCoefficients (L.coefficients z)
        (canonicalCurrentPoint C K z k) (canonicalReferencePoint C K z k)
        (n04CoordinatesCurrentHeightRatio C K z k)).a p =
          (L.coefficients (C.referenceState, 0)).a p ∧
      (reverseCoordinatePrincipalCoefficients (L.coefficients z)
        (canonicalCurrentPoint C K z k) (canonicalReferencePoint C K z k)
        (n04CoordinatesCurrentHeightRatio C K z k)).b p =
          (L.coefficients (C.referenceState, 0)).b p ∧
      (reverseCoordinatePrincipalCoefficients (L.coefficients z)
        (canonicalCurrentPoint C K z k) (canonicalReferencePoint C K z k)
        (n04CoordinatesCurrentHeightRatio C K z k)).c p =
          (L.coefficients (C.referenceState, 0)).c p := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hK : CanonicalGeometry D S C K base ε :=
    n04b_actualTypedAtlas_partA hT hS hN hfield e
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref := hN.1.1.2.2.1.stateSector
  have hfull (w : AnnularState S × ℝ) {p : PolarPoint}
      (hp : p ∈ physicalPieceOpen S K w k) :
      p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    apply n04b_typed_negative_domain_subset (D := D) (C := C)
      (Γ := n04bActualTravelChart S C L w) (m, side)
    simpa only [K, n04bActualTypedAtlas, n04bTypedAtlasData_physicalPieceOpen, hi] using hp
  dsimp only
  intro p hp
  exact canonicalRelativePrincipal_eq_of_negative_densities hK href hsref hz hs k
    (L.coefficients (C.referenceState, 0)) (L.coefficients z)
    (fun q hq => n04Coordinates_actualAtlas_negativePrincipalDensity
      hT hS hN hfield e href hsref k m side hi (hfull _ hq))
    (fun q hq => n04Coordinates_actualAtlas_negativePrincipalDensity
      hT hS hN hfield e hz hs k m side hi (hfull _ hq)) hp

end ContinuousFlexibility.Analysis
