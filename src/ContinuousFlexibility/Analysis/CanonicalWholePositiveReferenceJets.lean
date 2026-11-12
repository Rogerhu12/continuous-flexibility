import ContinuousFlexibility.Analysis.WholePositivePrincipalJetMatching
import ContinuousFlexibility.Analysis.CanonicalNegativeRelativeBoundaryJets
import ContinuousFlexibility.Analysis.PrincipalDensityGerms

/-!
# The actual positive principal difference vanishes to the matched order

The true whole negative root germ carries the proved reference principal
equation. The constructed positive coordinate and height jets transfer
that equation to the actual inverse-chart coefficient field. Interior
positive endpoints use their genuine negative neighbors; ambient endpoints
are explicitly excluded from this conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem adjugateCoordinatePrincipalCoefficients_component_eventuallyEq
    {A : SymmetricCoefficients} {F G : PolarPoint → PolarPoint}
    {h g : PolarPoint → ℝ} {p : PolarPoint}
    (hF : F =ᶠ[𝓝 p] G) (hh : h =ᶠ[𝓝 p] g) (i : Fin 3) :
    canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A F h) =ᶠ[𝓝 p]
      canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A G g) := by
  have hD : fderiv ℝ F =ᶠ[𝓝 p] fderiv ℝ G := hF.fderiv (𝕜 := ℝ)
  filter_upwards [hF, hD, hh] with q hpoint hderiv hheight
  unfold canonicalCoefficientComponent
  split_ifs <;>
    simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
      planeJacobian, hpoint, hderiv, hheight]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hT hS hN hfield e hz hs

/-- The whole-component negative selector has the same genuine root
germ as its stored endpoint field. Thus all reference principal jets
already proved for that field also hold for this actual selector. -/
theorem n04Coordinates_wholeNegativePrincipal_reference_root_jets
    (m : ℕ) (side : Bool) (θ : ℝ) (v : Fin 3) (k : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    iteratedFDeriv ℝ k
      (canonicalCoefficientComponent v (adjugateCoordinatePrincipalCoefficients
        (L.coefficients z) (canonicalWholeNegativeTransport C K z m)
        (canonicalWholeNegativeHeightRatio C K z m)))
        (if side then C.right m else C.left m, θ) =
      iteratedFDeriv ℝ k
        (canonicalCoefficientComponent v (L.coefficients (C.referenceState, 0)))
        (if side then C.right m else C.left m, θ) := by
  have hg := canonicalWholeNegativeTransport_root_germs hT hS hN hfield e
    (z := z) m side θ
  have hcoeff := adjugateCoordinatePrincipalCoefficients_component_eventuallyEq
    (A := L.coefficients z) hg.1 hg.2 v
  exact (hcoeff.iteratedFDeriv ℝ k).eq_of_nhds.trans
    (n04Coordinates_actualAtlas_relativeAdjugate_root_jets
      hT hS hN hfield e hz hs m side θ v k)

variable {n : ℕ} {i : N04PositiveComponent D.a D.b (deriv D.w)}
  (j : ∀ side, N04PositiveEndpointSource C i side)
  {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {c d J H : ℝ}
  (hm : WholePositiveTransportMatching n
    (fun side => n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
    (fun side => n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
    τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J H)

include j hm

/-- The positive field is compared to the original reference physical
coefficients. No unit principal field or coefficient-jet premise occurs. -/
theorem n04Coordinates_wholePositivePrincipal_reference_root_jets
    (m : ℕ) (side : Bool)
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m))
    (θ : ℝ) (v : Fin 3) :
    FiniteFullJetMatch n (if side then C.right m else C.left m, θ)
      (canonicalCoefficientComponent v (wholePositiveCanonicalCoefficients
        (L.coefficients z) τ σ Q))
      (canonicalCoefficientComponent v (L.coefficients (C.referenceState, 0))) := by
  have hmatch := n04Coordinates_wholePositivePrincipal_negative_root_jets
    hT hS hN hfield e hz hs j hm m side hadj θ v
  have hends := hN.1.1.2.2.2.1.1 m
  have hp : (if side then C.right m else C.left m, θ) ∈ annularOpen D := by
    refine ⟨?_, mem_univ _⟩
    cases side
    · exact ⟨hends.1, hends.2.1.trans hends.2.2⟩
    · exact ⟨hends.1.trans hends.2.1, hends.2.2⟩
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref := hN.1.1.2.2.1.stateSector
  have hA := hfield.smooth_coefficients (C.referenceState, 0) href hsref
  have hnhds := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have hAi : ContDiffAt ℝ ∞
      (canonicalCoefficientComponent v (L.coefficients (C.referenceState, 0)))
      (if side then C.right m else C.left m, θ) := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hA.1.contDiffAt hnhds
    · exact hA.2.1.contDiffAt hnhds
    · exact hA.2.2.contDiffAt hnhds
  refine ⟨hmatch.right_smooth, hAi, ?_⟩
  intro k hk
  exact (hmatch.jets k hk).symm.trans
    (n04Coordinates_wholeNegativePrincipal_reference_root_jets
      hT hS hN hfield e hz hs m side θ v k)

/-- The neighbor is supplied by the actual reference partition, not by
an additional principal matching assumption. -/
theorem n04Coordinates_wholePositivePrincipal_interior_endpoint_jets
    (side : Bool)
    (hinterior : n04PositiveEndpoint i side ≠ (if side then D.b else D.a))
    (θ : ℝ) (v : Fin 3) :
    FiniteFullJetMatch n (n04PositiveEndpoint i side, θ)
      (canonicalCoefficientComponent v (wholePositiveCanonicalCoefficients
        (L.coefficients z) τ σ Q))
      (canonicalCoefficientComponent v (L.coefficients (C.referenceState, 0))) := by
  obtain ⟨m, hadj⟩ := n04PositiveEndpoint_exists_negative_neighbor
    (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 i side hinterior
  have hadj' : n04PositiveEndpoint i (!(!side)) =
      (if !side then C.right m else C.left m) := by
    cases side <;> exact hadj
  have hpoint : (if !side then C.right m else C.left m) =
      n04PositiveEndpoint i side := by
    cases side <;> exact hadj.symm
  simpa only [hpoint] using
    (n04Coordinates_wholePositivePrincipal_reference_root_jets
      hT hS hN hfield e hz hs j hm m (!side) hadj' θ v)

/-- In particular, matching coordinate jets through order three and
height jets through order two gives the three genuine zero radial jets. -/
theorem n04Coordinates_wholePositivePrincipal_difference_endpoint_jets
    (side : Bool)
    (hinterior : n04PositiveEndpoint i side ≠ (if side then D.b else D.a))
    (θ : ℝ) (v : Fin 3) (k : ℕ) (hk : k ≤ n) :
    radialBoundaryJet
      (fun p => canonicalCoefficientComponent v
        (wholePositiveCanonicalCoefficients (L.coefficients z) τ σ Q) p -
          canonicalCoefficientComponent v (L.coefficients (C.referenceState, 0)) p)
      (n04PositiveEndpoint i side) k θ = 0 :=
  radialBoundaryJet_sub_eq_zero_of_finiteFullJetMatch
    (n04Coordinates_wholePositivePrincipal_interior_endpoint_jets
      hT hS hN hfield e hz hs j hm side hinterior θ v) hk

end ContinuousFlexibility.Analysis
