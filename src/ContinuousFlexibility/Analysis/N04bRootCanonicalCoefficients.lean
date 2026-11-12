import ContinuousFlexibility.Analysis.N04bSignedRootDensity
import ContinuousFlexibility.Analysis.N04bCanonicalOperator

/-!
# The signed root density at a canonical inverse point

The constructor's coefficient fields are the actual transported principal
density. The signed characteristic calculation consequently gives their
three frozen values at the canonical point. No canonical operator or
principal-density identity is assumed in this bridge.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The two endpoint orientations give the same canonical coefficient
triple. The inverse and forward chart identities identify the actual
physical point with the requested canonical point. -/
theorem n04bCanonicalOperatorData_root_coefficients
    {S : PhysicalSpacesData} (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (d v s : PolarPoint → ℝ)
    {U V : PolarPoint → ℝ} {x p : PolarPoint}
    (hInverse : K.inverseChart z m p = x) (hChart : K.chart z m x = p)
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d x + v x) * angularPartial U x)
    (hVr : radialPartial V x = -(d x - v x) * angularPartial V x)
    (hb : (L.coefficients z).b x = (L.coefficients z).a x * d x)
    (hc : (L.coefficients z).c x = (L.coefficients z).a x * (d x ^ 2 - v x ^ 2))
    (ha : 0 < (L.coefficients z).a x) (hv : 0 < v x) (hs : s x ≠ 0)
    (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x)
    (hr : fderiv ℝ (K.chart z m) x (1, 0) =
      (s x * (fderiv ℝ (characteristicTravelChart U V) x (1, 0)).1,
        (fderiv ℝ (characteristicTravelChart U V) x (1, 0)).2))
    (hθ : fderiv ℝ (K.chart z m) x (0, 1) =
      (s x * (fderiv ℝ (characteristicTravelChart U V) x (0, 1)).1,
        (fderiv ℝ (characteristicTravelChart U V) x (0, 1)).2))
    (hroot : |s x| ^ 2 * p.1 = 1)
    (hheight : K.height z m x = n04bSignedRootHeight (L.coefficients z) v s x) :
    ((n04bCanonicalOperatorData S L K).coefficients z m).a p = 1 ∧
      ((n04bCanonicalOperatorData S L K).coefficients z m).b p = 0 ∧
      ((n04bCanonicalOperatorData S L K).coefficients z m).c p = -p.1 := by
  have hroot' : |s x| ^ 2 * (K.chart z m x).1 = 1 := by
    simpa only [hChart] using hroot
  have hd := n04b_coordinatePrincipalDensity_signedRoot
    (L.coefficients z) (K.height z m) d v s
    hU hV hUr hVr hb hc ha hv hs hUθ hVθ hr hθ hroot' hheight
  simpa only [n04bCanonicalOperatorData, inverseChartPrincipalCoefficients,
    hInverse, hChart] using hd

end ContinuousFlexibility.Analysis
