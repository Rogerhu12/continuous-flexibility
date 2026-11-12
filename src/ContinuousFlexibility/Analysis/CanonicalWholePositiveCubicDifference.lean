import ContinuousFlexibility.Analysis.CanonicalWholePositiveReferenceJets
import ContinuousFlexibility.Analysis.WholePositivePrincipalExtension
import ContinuousFlexibility.Analysis.IntervalCubicGermDivision

/-!
# Actual cubic principal differences on an interior positive component

The numerator is the displayed positive chart's actual coefficient minus
the original physical reference coefficient. Its three zero endpoint
jets are consequences of the actual negative operator identity and the
constructed transport matching. A smooth representative supplies the
removable quotient and its fixed six-derivative estimate.

The component is buffered inside the annulus. This statement does not
claim the separate ambient-endpoint case or a material numerator bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def wholePositivePrincipalDifference (A Aref : SymmetricCoefficients)
    (τ σ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ) (v : Fin 3)
    (p : PolarPoint) : ℝ :=
  canonicalCoefficientComponent v (wholePositiveCanonicalCoefficients A τ σ Q) p -
    canonicalCoefficientComponent v Aref p

/-- The actual whole-positive field admits cubic division through both
true roots, with a globally smooth quotient representative. The mixed
estimate is expressed in the actual numerator, not the cutoff field. -/
theorem n04Coordinates_wholePositivePrincipal_cubic_difference
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
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {c d J H : ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      (fun side => n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J H)
    (hn : 2 ≤ n) (hl : D.a < n04PositiveLeft i) (hr : n04PositiveRight i < D.b) :
    ∃ divided : Fin 3 → PolarPoint → ℝ,
      (∀ v, ContDiff ℝ ∞ (divided v)) ∧
      (∀ v p, p ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) →
        wholePositivePrincipalDifference (L.coefficients z)
            (L.coefficients (C.referenceState, 0)) τ σ Q v p =
          ((p.1 - n04PositiveLeft i) * (n04PositiveRight i - p.1)) ^ 3 * divided v p) ∧
      ∀ v (a b : ℕ) (M : ℝ) p,
        p ∈ Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) →
        (∀ x ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
          |mixedDerivative (a + 6) b
            (wholePositivePrincipalDifference (L.coefficients z)
              (L.coefficients (C.referenceState, 0)) τ σ Q v) (x, p.2)| ≤ M) →
        |mixedDerivative a b (divided v) p| ≤ M / 36 := by
  have hD := n04b_profileGeometry_of_through03 hN
  have hcontinuous : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr := (n04PositiveComponent_bounds hcontinuous i).2.1
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref := hN.1.1.2.2.1.stateSector
  have hA := hfield.smooth_coefficients z hz hs
  have hAref := hfield.smooth_coefficients (C.referenceState, 0) href hsref
  obtain ⟨F, hF, he⟩ := exists_wholePositivePrincipal_difference_extension
    hl hlr hr (wholePositiveChartGeometry_of_matching hm)
    hA.1 hA.2.1 hA.2.2 hAref.1 hAref.2.1 hAref.2.2
  let f := wholePositivePrincipalDifference (L.coefficients z)
    (L.coefficients (C.referenceState, 0)) τ σ Q
  have hzero (side : Bool) (v : Fin 3) (θ : ℝ) (k : ℕ) (hk : k ≤ 2) :
      radialBoundaryJet (f v) (n04PositiveEndpoint i side) k θ = 0 := by
    have hinterior : n04PositiveEndpoint i side ≠ (if side then D.b else D.a) := by
      cases side
      · exact ne_of_gt hl
      · exact ne_of_lt hr
    exact n04Coordinates_wholePositivePrincipal_difference_endpoint_jets
      hT hS hN hfield e hz hs j hm side hinterior θ v k (hk.trans hn)
  have hleft (v : Fin 3) : ∀ θ k, k ≤ 2 →
      radialBoundaryJet (f v) (n04PositiveLeft i) k θ = 0 := by
    intro θ k hk
    simpa only [n04PositiveEndpoint, Bool.false_eq_true, ↓reduceIte] using
      hzero false v θ k hk
  have hright (v : Fin 3) : ∀ θ k, k ≤ 2 →
      radialBoundaryJet (f v) (n04PositiveRight i) k θ = 0 := by
    intro θ k hk
    simpa only [n04PositiveEndpoint, ↓reduceIte] using hzero true v θ k hk
  have hout (v : Fin 3) := intervalRadialCubicQuotient_of_closed_germs
    (f := f v) (hF v) hlr (he v) (hleft v) (hright v)
  refine ⟨fun v => intervalRadialCubicQuotient (F v)
    (n04PositiveLeft i) (n04PositiveRight i), fun v => (hout v).1, ?_, ?_⟩
  · intro v p hp
    exact (hout v).2.1 p hp
  · intro v a b M p hp hbound
    exact (hout v).2.2 a b M p hp hbound

end ContinuousFlexibility.Analysis
