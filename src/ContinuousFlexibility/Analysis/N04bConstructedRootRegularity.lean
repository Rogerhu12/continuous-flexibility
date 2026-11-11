import ContinuousFlexibility.Analysis.N04bConstructedRootDensity

/-!
# Regularity and Jacobian of the actual interior root chart

The open negative halves stay away from the zero root radius. Smoothness
there follows by composition with the explicit root coordinate, and the
Jacobian follows from its actual differential. The same statements handle
both orientations.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04b_contDiffAt_rootHalfCoordinate
    {T s : ℝ} {side : Bool} (hs : 0 < n04bTravelOrientation T side s) :
    ContDiffAt ℝ ∞ (n04bRootHalfCoordinate T side) s := by
  have horientation : ContDiffAt ℝ ∞ (n04bTravelOrientation T side) s := by
    cases side with
    | false => exact contDiffAt_id
    | true => exact contDiffAt_const.sub contDiffAt_id
  exact (n04b_contDiffAt_rootCoordinate hs).comp s horientation

theorem n04b_contDiffAt_rootPhysicalChart
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F x)
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    ContDiffAt ℝ ∞ (n04bRootPhysicalChart F T side) x := by
  exact ((n04b_contDiffAt_rootHalfCoordinate hs).comp x hF.fst).prodMk hF.snd

theorem n04b_contDiffAt_rootPhysicalHeight
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A.a x) (hv : ContDiffAt ℝ ∞ v x)
    (hF : ContDiffAt ℝ ∞ F x)
    (ha0 : 0 < A.a x) (hv0 : 0 < v x)
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    ContDiffAt ℝ ∞ (n04bRootPhysicalHeight A v F T side) x := by
  have hξ := (n04b_contDiffAt_rootPhysicalChart hF hs).fst
  have hξ0 := n04bRootPhysicalChart_fst_pos hs
  have hroot := hξ.sqrt hξ0.ne'
  have hroot0 := Real.sqrt_pos.mpr hξ0
  have hquot := (hA.mul hv).div hroot hroot0.ne'
  have hquot0 : 0 < A.a x * v x /
      Real.sqrt (n04bRootPhysicalChart F T side x).1 :=
    div_pos (mul_pos ha0 hv0) hroot0
  exact (hquot.sqrt hquot0.ne').inv (Real.sqrt_pos.mpr hquot0).ne'

theorem n04b_rootPhysicalChart_jacobian
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x)
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    planeJacobian (n04bRootPhysicalChart F T side) x =
      n04bRootDifferentialScale F T side x * planeJacobian F x :=
  planeJacobian_of_scaled_radial_differential
    (n04b_fderiv_rootPhysicalChart_apply hF hs (1, 0))
    (n04b_fderiv_rootPhysicalChart_apply hF hs (0, 1))

theorem n04b_rootPhysicalChart_jacobian_ne_zero
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x)
    (hs : 0 < n04bTravelOrientation T side (F x).1)
    (hJ : planeJacobian F x ≠ 0) :
    planeJacobian (n04bRootPhysicalChart F T side) x ≠ 0 := by
  rw [n04b_rootPhysicalChart_jacobian hF hs]
  exact mul_ne_zero (n04bRootDifferentialScale_ne_zero hs) hJ

theorem n04b_rootPhysicalChart_lift
    {F : PolarPoint → PolarPoint} (T : ℝ) (side : Bool) (P : ℝ)
    {x : PolarPoint} (hF : F (x + (0, P)) = F x + (0, P)) :
    n04bRootPhysicalChart F T side (x + (0, P)) =
      n04bRootPhysicalChart F T side x + (0, P) := by
  simp only [n04bRootPhysicalChart, hF, n04bRootStripChart,
    Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, add_zero]

theorem n04b_rootPhysicalChart_reflection
    {F : PolarPoint → PolarPoint} (T : ℝ) (side : Bool)
    {x : PolarPoint} (hF : F (x.1, -x.2) = ((F x).1, -(F x).2)) :
    n04bRootPhysicalChart F T side (x.1, -x.2) =
      ((n04bRootPhysicalChart F T side x).1,
        -(n04bRootPhysicalChart F T side x).2) := by
  simp only [n04bRootPhysicalChart, Function.comp_def, hF, n04bRootStripChart]

theorem n04b_rootPhysicalHeight_lift
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} (T : ℝ) (side : Bool) (P : ℝ)
    {x : PolarPoint} (hA : A.a (x + (0, P)) = A.a x)
    (hv : v (x + (0, P)) = v x)
    (hF : F (x + (0, P)) = F x + (0, P)) :
    n04bRootPhysicalHeight A v F T side (x + (0, P)) =
      n04bRootPhysicalHeight A v F T side x := by
  simp only [n04bRootPhysicalHeight, hA, hv,
    n04b_rootPhysicalChart_lift T side P hF, Prod.fst_add, add_zero]

theorem n04b_rootPhysicalHeight_reflection
    {A : SymmetricCoefficients} {v : PolarPoint → ℝ}
    {F : PolarPoint → PolarPoint} (T : ℝ) (side : Bool)
    {x : PolarPoint} (hA : A.a (x.1, -x.2) = A.a x)
    (hv : v (x.1, -x.2) = v x)
    (hF : F (x.1, -x.2) = ((F x).1, -(F x).2)) :
    n04bRootPhysicalHeight A v F T side (x.1, -x.2) =
      n04bRootPhysicalHeight A v F T side x := by
  simp only [n04bRootPhysicalHeight, hA, hv,
    n04b_rootPhysicalChart_reflection T side hF]

end ContinuousFlexibility.Analysis
