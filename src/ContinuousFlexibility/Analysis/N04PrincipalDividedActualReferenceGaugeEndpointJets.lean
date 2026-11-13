import ContinuousFlexibility.Analysis.CanonicalWholePositiveReferenceJets
import ContinuousFlexibility.Analysis.N04PrincipalDividedRadialGaugePrincipalFiniteJets
import ContinuousFlexibility.Analysis.PositiveReferencePhysicalLower

/-!
# Actual endpoint jets after the fixed reference normalization

The reference range certificate determines the true inverse images of
the canonical endpoints. The actual relative principal jets there are
transported by one common fixed radial gauge. Both coefficient fields
are the displayed current and reference fields of that same gauge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Coordinates_referenceGaugePrincipal_endpoint_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss n : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {τ σ τ₀ σ₀ : PolarPoint → PolarPoint} {Q Q₀ : PolarPoint → ℝ}
    {c d J H c₀ d₀ : ℝ} {Y H₀ : ℝ → ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      (fun side => n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J H)
    (hgeometry₀ : WholePositiveChartGeometry σ₀ τ₀
      (wholePositiveChartHeight σ₀ Q₀) (n04PositiveLeft i) (n04PositiveRight i) c₀ d₀)
    (hτ₀ : τ₀ = id) (hσ₀ : σ₀ = id) (hQ₀ : Q₀ = (fun _ => 1))
    (hG : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H₀ p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (side : Bool)
    (hinterior : n04PositiveEndpoint i side ≠ (if side then D.b else D.a))
    (θ : ℝ) (v : Fin 3) :
    let B := inverseChartPrincipalCoefficients (L.coefficients z)
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
      (wholePositiveReferenceGaugeInverse τ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ Q)
    let B₀ := inverseChartPrincipalCoefficients (L.coefficients (C.referenceState, 0))
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ₀)
      (wholePositiveReferenceGaugeInverse τ₀ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ₀ Q₀)
    FiniteFullJetMatch n ((if side then (1 : ℝ) else 0), θ)
      (canonicalCoefficientComponent v B) (canonicalCoefficientComponent v B₀) := by
  have hD := n04b_profileGeometry_of_through03 hN
  have hcontinuous : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr := (n04PositiveComponent_bounds hcontinuous i).2.1
  have hY : ContDiff ℝ ∞ Y := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def, id_eq] using
      hG.chart_smooth.fst.comp (contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))))
  have hH₀ : ContDiff ℝ ∞ H₀ := by
    simpa only [Function.comp_def, id_eq] using
      hG.height_smooth.comp (contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))))
  have hYpos (r : ℝ) : 0 < deriv Y r := by
    simpa only [planeJacobian_positiveReferenceCylinderChart (p := (r, 0))
      (hY.differentiable (by simp) r)] using hG.jacobian_positive (r, 0)
  have hends := hG.cylinder_endpoint_values hlr
  have hpoint : positiveReferenceCylinderInverse Y ((if side then (1 : ℝ) else 0), θ) =
      (n04PositiveEndpoint i side, θ) := by
    have he := hG.left_inverse (n04PositiveEndpoint i side, θ)
    cases side <;>
      simpa only [n04PositiveEndpoint, Bool.false_eq_true, ↓reduceIte,
        positiveReferenceCylinderChart, hends.1, hends.2] using he
  have href := (wholePositiveCanonicalFields_reference
    (L.coefficients (C.referenceState, 0)) hτ₀ hσ₀ hQ₀).2.1
  have hmatch : FiniteFullJetMatch n
      (positiveReferenceCylinderInverse Y ((if side then (1 : ℝ) else 0), θ))
      (canonicalCoefficientComponent v
        (wholePositiveCanonicalCoefficients (L.coefficients z) τ σ Q))
      (canonicalCoefficientComponent v
        (wholePositiveCanonicalCoefficients (L.coefficients (C.referenceState, 0))
          τ₀ σ₀ Q₀)) := by
    rw [hpoint, href]
    exact n04Coordinates_wholePositivePrincipal_interior_endpoint_jets
      hT hS hN hfield e hz hs j hm side hinterior θ v
  exact finiteFullJetMatch_wholePositiveReferenceGauge_principal
    (wholePositiveChartGeometry_of_matching hm) hgeometry₀ hY hH₀
    hG.inverse_smooth hYpos v hmatch

end ContinuousFlexibility.Analysis
