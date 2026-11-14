module

public import ContinuousFlexibility.Analysis.CharacteristicRootDensity

/-!
# One principal-density normalization for both root orientations

The radial differential may be multiplied by either sign. Its absolute
value enters the transformed density and the positive height, while the
mixed coefficient changes by the orientation sign. The same calculation
therefore gives the Tricomi principal density at both roots.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The signed version of radial differential scaling. It is a formula
for the actual derivatives of two coordinate maps. -/
theorem n04b_coordinatePrincipalDensity_signedRadialScale
    (A : SymmetricCoefficients) (h : PolarPoint → ℝ)
    {F G : PolarPoint → PolarPoint} {x : PolarPoint} {s : ℝ}
    (hs : s ≠ 0) (hJ : planeJacobian F x ≠ 0)
    (hr : fderiv ℝ G x (1, 0) =
      (s * (fderiv ℝ F x (1, 0)).1, (fderiv ℝ F x (1, 0)).2))
    (hθ : fderiv ℝ G x (0, 1) =
      (s * (fderiv ℝ F x (0, 1)).1, (fderiv ℝ F x (0, 1)).2)) :
    (coordinatePrincipalDensity A G h).a x =
        |s| * (coordinatePrincipalDensity A F h).a x ∧
      (coordinatePrincipalDensity A G h).b x =
        (s / |s|) * (coordinatePrincipalDensity A F h).b x ∧
      (coordinatePrincipalDensity A G h).c x =
        (coordinatePrincipalDensity A F h).c x / |s| := by
  have hAbs : |planeJacobian G x| = |s| * |planeJacobian F x| := by
    rw [planeJacobian_of_scaled_radial_differential hr hθ, abs_mul]
  have hs0 : |s| ≠ 0 := abs_ne_zero.mpr hs
  have hJ0 := abs_ne_zero.mpr hJ
  simp only [coordinatePrincipalDensity, coefficientQuadratic, hAbs, hr, hθ]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    field_simp [hs, hs0, hJ0]
    <;> ring_nf
    <;> simp only [sq_abs]
    <;> ring

/-- The physical root height uses the magnitude of the radial scale. -/
def n04bSignedRootHeight (A : SymmetricCoefficients)
    (v s : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (Real.sqrt (A.a x * v x * |s x|))⁻¹

theorem n04bSignedRootHeight_pos
    {A : SymmetricCoefficients} {v s : PolarPoint → ℝ} {x : PolarPoint}
    (ha : 0 < A.a x) (hv : 0 < v x) (hs : s x ≠ 0) :
    0 < n04bSignedRootHeight A v s x :=
  characteristicRootHeight_pos (s := fun y => |s y|) ha hv (abs_pos.mpr hs)

theorem n04bSignedRootHeight_normalization
    {A : SymmetricCoefficients} {v s : PolarPoint → ℝ} {x : PolarPoint}
    (ha : 0 < A.a x) (hv : 0 < v x) (hs : s x ≠ 0) :
    n04bSignedRootHeight A v s x ^ 2 * (A.a x * v x * |s x|) = 1 :=
  characteristicRootHeight_normalization (s := fun y => |s y|) ha hv (abs_pos.mpr hs)

/-- One signed differential and one explicit positive height give the
normal principal coefficients on either side of a cut. The height need
only be identified at the point, since principal density uses its value. -/
theorem n04b_coordinatePrincipalDensity_signedRoot
    (A : SymmetricCoefficients) (h d v s : PolarPoint → ℝ)
    {U V : PolarPoint → ℝ} {G : PolarPoint → PolarPoint} {x : PolarPoint}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d x + v x) * angularPartial U x)
    (hVr : radialPartial V x = -(d x - v x) * angularPartial V x)
    (hb : A.b x = A.a x * d x)
    (hc : A.c x = A.a x * (d x ^ 2 - v x ^ 2))
    (ha : 0 < A.a x) (hv : 0 < v x) (hs : s x ≠ 0)
    (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x)
    (hr : fderiv ℝ G x (1, 0) =
      (s x * (fderiv ℝ (characteristicTravelChart U V) x (1, 0)).1,
        (fderiv ℝ (characteristicTravelChart U V) x (1, 0)).2))
    (hθ : fderiv ℝ G x (0, 1) =
      (s x * (fderiv ℝ (characteristicTravelChart U V) x (0, 1)).1,
        (fderiv ℝ (characteristicTravelChart U V) x (0, 1)).2))
    (hroot : |s x| ^ 2 * (G x).1 = 1)
    (hheight : h x = n04bSignedRootHeight A v s x) :
    (coordinatePrincipalDensity A G h).a x = 1 ∧
      (coordinatePrincipalDensity A G h).b x = 0 ∧
      (coordinatePrincipalDensity A G h).c x = -(G x).1 := by
  have hJ : planeJacobian (characteristicTravelChart U V) x ≠ 0 :=
    ne_of_gt (planeJacobian_characteristicTravelChart_pos hU hV hUr hVr hv hUθ hVθ)
  have hw := coordinatePrincipalDensity_characteristicTravelChart
    A h hU hV hUr hVr hb hc hv hUθ hVθ
  have hd := n04b_coordinatePrincipalDensity_signedRadialScale A h hs hJ hr hθ
  have hn : h x ^ 2 * (A.a x * v x * |s x|) = 1 := by
    rw [hheight]
    exact n04bSignedRootHeight_normalization ha hv hs
  have hs0 : |s x| ≠ 0 := abs_ne_zero.mpr hs
  have hq : h x ^ 2 * A.a x * v x = (G x).1 * |s x| := by
    apply mul_right_cancel₀ hs0
    nlinarith only [hn, hroot]
  refine ⟨?_, ?_, ?_⟩
  · rw [hd.1, hw.1]
    nlinarith only [hn]
  · rw [hd.2.1, hw.2.1, mul_zero]
  · rw [hd.2.2, hw.2.2, hq]
    field_simp [hs0]
    <;> ring

end ContinuousFlexibility.Analysis
