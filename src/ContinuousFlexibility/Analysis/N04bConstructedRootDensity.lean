import ContinuousFlexibility.Analysis.N04bRootTravelDifferential
import ContinuousFlexibility.Analysis.N04bRootCanonicalCoefficients

/-!
# Principal coefficients of the constructed characteristic root chart

The root chart and height in this file are explicit functions. Their
principal density is derived from the actual characteristic equations.
The two directional scaling identities and the root normalization are
proved consequences of the constructed chart, rather than premises.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The positive physical height determined by the actual root coordinate. -/
def n04bRootPhysicalHeight (A : SymmetricCoefficients) (v : PolarPoint → ℝ)
    (F : PolarPoint → PolarPoint) (T : ℝ) (side : Bool) (x : PolarPoint) : ℝ :=
  (Real.sqrt (A.a x * v x /
    Real.sqrt (n04bRootPhysicalChart F T side x).1))⁻¹

theorem n04bRootPhysicalHeight_eq_signed
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    n04bRootPhysicalHeight A v F T side x =
      n04bSignedRootHeight A v (n04bRootDifferentialScale F T side) x := by
  simp only [n04bRootPhysicalHeight, n04bSignedRootHeight,
    n04bRootDifferentialScale_abs hs, div_eq_mul_inv]

theorem n04bRootPhysicalHeight_pos
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (ha : 0 < A.a x) (hv : 0 < v x)
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    0 < n04bRootPhysicalHeight A v F T side x := by
  rw [n04bRootPhysicalHeight_eq_signed hs]
  exact n04bSignedRootHeight_pos ha hv (n04bRootDifferentialScale_ne_zero hs)

theorem n04b_differentiableAt_characteristicTravelChart
    {U V : PolarPoint → ℝ} {x : PolarPoint}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    DifferentiableAt ℝ (characteristicTravelChart U V) x := by
  have hd := ((hV.hasFDerivAt.fun_sub hU.hasFDerivAt).const_mul (1 / 2 : ℝ)).prodMk
    ((hU.hasFDerivAt.fun_add hV.hasFDerivAt).const_mul (1 / 2 : ℝ))
  exact hd.differentiableAt

/-- The constructed root chart with its constructed height has the
canonical triple (1, 0, -ξ), for either orientation. -/
theorem n04b_coordinatePrincipalDensity_constructedRoot
    (A : SymmetricCoefficients) (d v : PolarPoint → ℝ) (T : ℝ) (side : Bool)
    {U V : PolarPoint → ℝ} {x : PolarPoint}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d x + v x) * angularPartial U x)
    (hVr : radialPartial V x = -(d x - v x) * angularPartial V x)
    (hb : A.b x = A.a x * d x)
    (hc : A.c x = A.a x * (d x ^ 2 - v x ^ 2))
    (ha : 0 < A.a x) (hv : 0 < v x)
    (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x)
    (hs : 0 < n04bTravelOrientation T side (characteristicTravelChart U V x).1) :
    (coordinatePrincipalDensity A
      (n04bRootPhysicalChart (characteristicTravelChart U V) T side)
      (n04bRootPhysicalHeight A v (characteristicTravelChart U V) T side)).a x = 1 ∧
    (coordinatePrincipalDensity A
      (n04bRootPhysicalChart (characteristicTravelChart U V) T side)
      (n04bRootPhysicalHeight A v (characteristicTravelChart U V) T side)).b x = 0 ∧
    (coordinatePrincipalDensity A
      (n04bRootPhysicalChart (characteristicTravelChart U V) T side)
      (n04bRootPhysicalHeight A v (characteristicTravelChart U V) T side)).c x =
        -(n04bRootPhysicalChart (characteristicTravelChart U V) T side x).1 := by
  have hF := n04b_differentiableAt_characteristicTravelChart hU hV
  exact n04b_coordinatePrincipalDensity_signedRoot A
    (n04bRootPhysicalHeight A v (characteristicTravelChart U V) T side) d v
    (n04bRootDifferentialScale (characteristicTravelChart U V) T side)
    hU hV hUr hVr hb hc ha hv (n04bRootDifferentialScale_ne_zero hs) hUθ hVθ
    (n04b_fderiv_rootPhysicalChart_apply hF hs (1, 0))
    (n04b_fderiv_rootPhysicalChart_apply hF hs (0, 1))
    (n04bRootDifferentialScale_normalization hs)
    (n04bRootPhysicalHeight_eq_signed hs)

/-- At an actual canonical inverse point, the constructed chart germ and
height value suffice to identify all three coefficient fields. No operator
identity or directional differential identity is assumed. -/
theorem n04bCanonicalOperatorData_constructedRoot_coefficients
    {S : PhysicalSpacesData} (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (d v : PolarPoint → ℝ)
    (T : ℝ) (side : Bool) {U V : PolarPoint → ℝ} {x p : PolarPoint}
    (hInverse : K.inverseChart z m p = x) (hChart : K.chart z m x = p)
    (hConstructed : K.chart z m =ᶠ[𝓝 x]
      n04bRootPhysicalChart (characteristicTravelChart U V) T side)
    (hHeight : K.height z m x =
      n04bRootPhysicalHeight (L.coefficients z) v
        (characteristicTravelChart U V) T side x)
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d x + v x) * angularPartial U x)
    (hVr : radialPartial V x = -(d x - v x) * angularPartial V x)
    (hb : (L.coefficients z).b x = (L.coefficients z).a x * d x)
    (hc : (L.coefficients z).c x = (L.coefficients z).a x * (d x ^ 2 - v x ^ 2))
    (ha : 0 < (L.coefficients z).a x) (hv : 0 < v x)
    (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x)
    (hs : 0 < n04bTravelOrientation T side (characteristicTravelChart U V x).1) :
    ((n04bCanonicalOperatorData S L K).coefficients z m).a p = 1 ∧
      ((n04bCanonicalOperatorData S L K).coefficients z m).b p = 0 ∧
      ((n04bCanonicalOperatorData S L K).coefficients z m).c p = -p.1 := by
  have hF := n04b_differentiableAt_characteristicTravelChart hU hV
  have hD : fderiv ℝ (K.chart z m) x =
      fderiv ℝ (n04bRootPhysicalChart (characteristicTravelChart U V) T side) x :=
    hConstructed.fderiv_eq
  have hpoint : n04bRootPhysicalChart (characteristicTravelChart U V) T side x = p :=
    hConstructed.self_of_nhds.symm.trans hChart
  have hroot :
      |n04bRootDifferentialScale (characteristicTravelChart U V) T side x| ^ 2 *
        p.1 = 1 := by
    simpa only [hpoint] using n04bRootDifferentialScale_normalization hs
  refine n04bCanonicalOperatorData_root_coefficients L K z m d v
    (n04bRootDifferentialScale (characteristicTravelChart U V) T side)
    hInverse hChart hU hV hUr hVr hb hc ha hv
    (n04bRootDifferentialScale_ne_zero hs) hUθ hVθ ?_ ?_ hroot ?_
  · rw [hD]
    exact n04b_fderiv_rootPhysicalChart_apply hF hs (1, 0)
  · rw [hD]
    exact n04b_fderiv_rootPhysicalChart_apply hF hs (0, 1)
  · exact hHeight.trans (n04bRootPhysicalHeight_eq_signed hs)

end ContinuousFlexibility.Analysis
