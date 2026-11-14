module

public import ContinuousFlexibility.Analysis.CharacteristicPrincipalDensity
public import ContinuousFlexibility.Analysis.ScaledRadialPrincipalDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The explicit height that normalizes a characteristic root chart

The root chart's actual radial differential is a positive scale s of the
travel differential, and s² ξ = 1. The physical height is the reciprocal
square root of a v s. Its principal density is exactly diag(1,-ξ).
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

/-- Physical height for a root chart with positive radial scale. -/
def characteristicRootHeight (A : SymmetricCoefficients)
    (v s : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (Real.sqrt (A.a x * v x * s x))⁻¹

theorem characteristicRootHeight_pos
    {A : SymmetricCoefficients} {v s : PolarPoint → ℝ} {x : PolarPoint}
    (ha : 0 < A.a x) (hv : 0 < v x) (hs : 0 < s x) :
    0 < characteristicRootHeight A v s x := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (mul_pos (mul_pos ha hv) hs))

theorem characteristicRootHeight_normalization
    {A : SymmetricCoefficients} {v s : PolarPoint → ℝ} {x : PolarPoint}
    (ha : 0 < A.a x) (hv : 0 < v x) (hs : 0 < s x) :
    characteristicRootHeight A v s x ^ 2 * (A.a x * v x * s x) = 1 := by
  have hp : 0 < A.a x * v x * s x := mul_pos (mul_pos ha hv) hs
  rw [characteristicRootHeight, inv_pow, Real.sq_sqrt hp.le]
  exact inv_mul_cancel₀ (ne_of_gt hp)

/-- The displayed height is smooth wherever its three actual factors
are smooth and positive. -/
theorem contDiffAt_characteristicRootHeight
    {A : SymmetricCoefficients} {v s : PolarPoint → ℝ} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A.a x) (hv : ContDiffAt ℝ ∞ v x)
    (hs : ContDiffAt ℝ ∞ s x)
    (ha0 : 0 < A.a x) (hv0 : 0 < v x) (hs0 : 0 < s x) :
    ContDiffAt ℝ ∞ (characteristicRootHeight A v s) x := by
  have hp : 0 < A.a x * v x * s x := mul_pos (mul_pos ha0 hv0) hs0
  have hprod := (hA.mul hv).mul hs
  have hroot : ContDiffAt ℝ ∞ (fun y => Real.sqrt (A.a y * v y * s y)) x := by
    simpa only [Real.sqrt_eq_rpow] using
      hprod.rpow_const_of_ne (p := (1 / 2 : ℝ)) (ne_of_gt hp)
  exact hroot.fun_inv (ne_of_gt (Real.sqrt_pos.2 hp))

/-- The diagonal canonical form follows from actual characteristic
equations, the actual root differential, and the explicit height. -/
theorem coordinatePrincipalDensity_characteristicRoot
    (A : SymmetricCoefficients) (d v s : PolarPoint → ℝ)
    {U V : PolarPoint → ℝ} {G : PolarPoint → PolarPoint} {x : PolarPoint}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hUr : radialPartial U x = -(d x + v x) * angularPartial U x)
    (hVr : radialPartial V x = -(d x - v x) * angularPartial V x)
    (hb : A.b x = A.a x * d x) (hc : A.c x = A.a x * (d x ^ 2 - v x ^ 2))
    (ha : 0 < A.a x) (hv : 0 < v x) (hs : 0 < s x)
    (hUθ : 0 < angularPartial U x) (hVθ : 0 < angularPartial V x)
    (hr : fderiv ℝ G x (1, 0) =
      (s x * (fderiv ℝ (characteristicTravelChart U V) x (1, 0)).1,
        (fderiv ℝ (characteristicTravelChart U V) x (1, 0)).2))
    (hθ : fderiv ℝ G x (0, 1) =
      (s x * (fderiv ℝ (characteristicTravelChart U V) x (0, 1)).1,
        (fderiv ℝ (characteristicTravelChart U V) x (0, 1)).2))
    (hroot : s x ^ 2 * (G x).1 = 1) :
    (coordinatePrincipalDensity A G (characteristicRootHeight A v s)).a x = 1 ∧
      (coordinatePrincipalDensity A G (characteristicRootHeight A v s)).b x = 0 ∧
      (coordinatePrincipalDensity A G (characteristicRootHeight A v s)).c x = -(G x).1 := by
  have hJ : planeJacobian (characteristicTravelChart U V) x ≠ 0 :=
    ne_of_gt (planeJacobian_characteristicTravelChart_pos hU hV hUr hVr hv hUθ hVθ)
  have hw := coordinatePrincipalDensity_characteristicTravelChart
    A (characteristicRootHeight A v s) hU hV hUr hVr hb hc hv hUθ hVθ
  have hd := coordinatePrincipalDensity_of_scaled_radial_differential
    A (characteristicRootHeight A v s) hs hJ hr hθ
  have hn := characteristicRootHeight_normalization ha hv hs
  have hs0 := ne_of_gt hs
  have hq : characteristicRootHeight A v s x ^ 2 * A.a x * v x = (G x).1 * s x := by
    apply mul_right_cancel₀ hs0
    nlinarith only [hn, hroot]
  refine ⟨?_, ?_, ?_⟩
  · rw [hd.1, hw.1]
    nlinarith only [hn]
  · rw [hd.2.1, hw.2.1]
  · rw [hd.2.2, hw.2.2, hq]
    field_simp [hs0]
    <;> ring

end ContinuousFlexibility.Analysis
