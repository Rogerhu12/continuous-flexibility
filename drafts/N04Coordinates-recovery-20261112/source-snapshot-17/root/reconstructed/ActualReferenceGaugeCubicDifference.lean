import ContinuousFlexibility.Analysis.ActualReferenceGaugeEndpointJets
import ContinuousFlexibility.Analysis.RadialGaugePrincipalDifferenceExtension
import ContinuousFlexibility.Analysis.IntervalCubicGermDivision

/-!
# The actual fixed-reference principal numerator is cubically divisible

The true canonical endpoint jets and the true closed-cylinder germs
come from the same displayed reference gauge. Cubic division therefore
applies to the actual current-minus-reference principal fields. Its
mixed estimate uses six additional radial derivatives of that actual
numerator and no angular derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Coordinates_referenceGaugePrincipal_cubic_difference
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
    (hn : 2 ≤ n) (hl : D.a < n04PositiveLeft i) (hr : n04PositiveRight i < D.b) :
    let B := inverseChartPrincipalCoefficients (L.coefficients z)
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
      (wholePositiveReferenceGaugeInverse τ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ Q)
    let B₀ := inverseChartPrincipalCoefficients (L.coefficients (C.referenceState, 0))
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ₀)
      (wholePositiveReferenceGaugeInverse τ₀ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ₀ Q₀)
    ∃ divided : Fin 3 → PolarPoint → ℝ,
      (∀ v, ContDiff ℝ ∞ (divided v)) ∧
      (∀ v p, p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) →
        canonicalCoefficientComponent v B p - canonicalCoefficientComponent v B₀ p =
          (p.1 * (1 - p.1)) ^ 3 * divided v p) ∧
      ∀ v (a b : ℕ) (M : ℝ) p,
        p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) →
        (∀ x ∈ Icc (0 : ℝ) 1,
          |mixedDerivative (a + 6) b (fun q =>
            canonicalCoefficientComponent v B q - canonicalCoefficientComponent v B₀ q)
              (x, p.2)| ≤ M) →
        |mixedDerivative a b (divided v) p| ≤ M / 36 := by
  let B := inverseChartPrincipalCoefficients (L.coefficients z)
    (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
    (wholePositiveReferenceGaugeInverse τ (positiveReferenceCylinderInverse Y))
    (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ Q)
  let B₀ := inverseChartPrincipalCoefficients (L.coefficients (C.referenceState, 0))
    (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ₀)
    (wholePositiveReferenceGaugeInverse τ₀ (positiveReferenceCylinderInverse Y))
    (wholePositiveReferenceGaugeHeight (fun p : PolarPoint => H₀ p.1) σ₀ Q₀)
  let f := fun v p => canonicalCoefficientComponent v B p - canonicalCoefficientComponent v B₀ p
  have hD := n04b_profileGeometry_of_through03 hN
  have hcontinuous : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr := (n04PositiveComponent_bounds hcontinuous i).2.1
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref := hN.1.1.2.2.1.stateSector
  have hA := hfield.smooth_coefficients z hz hs
  have hA₀ := hfield.smooth_coefficients (C.referenceState, 0) href hsref
  obtain ⟨F, hF, he⟩ := exists_referenceGaugePrincipal_difference_extension
    hl hlr hr (wholePositiveChartGeometry_of_matching hm) hgeometry₀ hτ₀ hσ₀ hQ₀ hG
    hA.1 hA.2.1 hA.2.2 hA₀.1 hA₀.2.1 hA₀.2.2
  have hzero (side : Bool) (v : Fin 3) (θ : ℝ) (k : ℕ) (hk : k ≤ 2) :
      radialBoundaryJet (f v) (if side then 1 else 0) k θ = 0 := by
    have hinterior : n04PositiveEndpoint i side ≠ (if side then D.b else D.a) := by
      cases side
      · exact ne_of_gt hl
      · exact ne_of_lt hr
    exact radialBoundaryJet_sub_eq_zero_of_finiteFullJetMatch
      (n04Coordinates_referenceGaugePrincipal_endpoint_jets
        hT hS hN hfield e hz hs j hm hgeometry₀ hτ₀ hσ₀ hQ₀ hG
        side hinterior θ v) (hk.trans hn)
  have hleft (v : Fin 3) : ∀ θ k, k ≤ 2 → radialBoundaryJet (f v) 0 k θ = 0 := by
    intro θ k hk
    exact hzero false v θ k hk
  have hright (v : Fin 3) : ∀ θ k, k ≤ 2 → radialBoundaryJet (f v) 1 k θ = 0 := by
    intro θ k hk
    exact hzero true v θ k hk
  have hout (v : Fin 3) := intervalRadialCubicQuotient_of_closed_germs
    (f := f v) (hF v) (by norm_num : (0 : ℝ) < 1) (he v) (hleft v) (hright v)
  refine ⟨fun v => intervalRadialCubicQuotient (F v) 0 1,
    fun v => (hout v).1, ?_, ?_⟩
  · intro v p hp
    simpa only [sub_zero] using (hout v).2.1 p hp
  · intro v a b M p hp hbound
    exact (hout v).2.2 a b M p hp hbound

end ContinuousFlexibility.Analysis
