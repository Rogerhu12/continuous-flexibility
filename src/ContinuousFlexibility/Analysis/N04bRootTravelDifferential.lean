module

public import ContinuousFlexibility.Analysis.N04bRootReparametrization
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Tactic.Convert

/-!
# Differentials of the constructed root travel charts

The forward root coordinate is differentiated using its proved inverse,
whose derivative is the square root. A single signed chain rule therefore
computes the actual constructed chart on both moving travel halves.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04bRootCoordinate_pos {s : ℝ} (hs : 0 < s) :
    0 < n04bRootCoordinate s := by
  exact Real.rpow_pos_of_pos (by positivity : 0 < 3 * s / 2) _

/-- The actual inverse identity determines the derivative of the forward
root coordinate; no scaling relation is supplied as a hypothesis. -/
theorem n04b_hasDerivAt_rootCoordinate {s : ℝ} (hs : 0 < s) :
    HasDerivAt n04bRootCoordinate
      (Real.sqrt (n04bRootCoordinate s))⁻¹ s := by
  have hp := n04bRootCoordinate_pos hs
  have hi : ∀ᶠ y in 𝓝 s, n04bRootTravel (n04bRootCoordinate y) = y := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with y hy
    exact n04b_rootTravel_rootCoordinate hy.le
  exact HasDerivAt.of_local_left_inverse
    (n04b_contDiffAt_rootCoordinate hs).continuousAt
    (n04b_hasDerivAt_rootTravel hp)
    (ne_of_gt (Real.sqrt_pos.2 hp)) hi

theorem n04b_hasDerivAt_travelOrientation (T : ℝ) (side : Bool) (s : ℝ) :
    HasDerivAt (n04bTravelOrientation T side)
      (if side then (-1 : ℝ) else 1) s := by
  cases side with
  | false => exact hasDerivAt_id s
  | true => exact (hasDerivAt_id s).const_sub T

theorem n04b_hasDerivAt_rootHalfCoordinate
    {T s : ℝ} {side : Bool} (hs : 0 < n04bTravelOrientation T side s) :
    HasDerivAt (n04bRootHalfCoordinate T side)
      ((if side then (-1 : ℝ) else 1) /
        Real.sqrt (n04bRootHalfCoordinate T side s)) s := by
  have hd := (n04b_hasDerivAt_rootCoordinate hs).comp s
    (n04b_hasDerivAt_travelOrientation T side s)
  change HasDerivAt
    (fun y => n04bRootCoordinate (n04bTravelOrientation T side y)) _ s
  apply hd.congr_deriv
  simp only [n04bRootHalfCoordinate, div_eq_mul_inv]
  ring

/-- The signed scale is a defined function of the actual root chart. -/
def n04bRootDifferentialScale (F : PolarPoint → PolarPoint)
    (T : ℝ) (side : Bool) (x : PolarPoint) : ℝ :=
  (if side then -1 else 1) /
    Real.sqrt (n04bRootPhysicalChart F T side x).1

theorem n04bRootPhysicalChart_fst_pos
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    0 < (n04bRootPhysicalChart F T side x).1 :=
  n04bRootCoordinate_pos hs

/-- An arbitrary direction is handled once, so radial and angular
differentials are consequences of the same actual chain rule. -/
theorem n04b_fderiv_rootPhysicalChart_apply
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x)
    (hs : 0 < n04bTravelOrientation T side (F x).1) (q : PolarPoint) :
    fderiv ℝ (n04bRootPhysicalChart F T side) x q =
      (n04bRootDifferentialScale F T side x * (fderiv ℝ F x q).1,
        (fderiv ℝ F x q).2) := by
  have hfirst := (n04b_hasDerivAt_rootHalfCoordinate hs).comp_hasFDerivAt x
    hF.hasFDerivAt.fst
  have hd := hfirst.prodMk hF.hasFDerivAt.snd
  have he := DFunLike.congr_fun hd.fderiv q
  simpa only [n04bRootPhysicalChart, n04bRootStripChart,
    n04bRootDifferentialScale, Function.comp_def,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul] using! he

theorem n04bRootDifferentialScale_ne_zero
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    n04bRootDifferentialScale F T side x ≠ 0 := by
  apply div_ne_zero
  · cases side <;> norm_num
  · exact ne_of_gt (Real.sqrt_pos.2 (n04bRootPhysicalChart_fst_pos hs))

theorem n04bRootDifferentialScale_abs
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    |n04bRootDifferentialScale F T side x| =
      (Real.sqrt (n04bRootPhysicalChart F T side x).1)⁻¹ := by
  have hp := Real.sqrt_pos.2 (n04bRootPhysicalChart_fst_pos hs)
  rw [n04bRootDifferentialScale, abs_div, abs_of_pos hp]
  have hsign : |if side then (-1 : ℝ) else 1| = 1 := by
    cases side <;> norm_num
  rw [hsign, one_div]

theorem n04bRootDifferentialScale_normalization
    {F : PolarPoint → PolarPoint} {T : ℝ} {side : Bool} {x : PolarPoint}
    (hs : 0 < n04bTravelOrientation T side (F x).1) :
    |n04bRootDifferentialScale F T side x| ^ 2 *
      (n04bRootPhysicalChart F T side x).1 = 1 := by
  have hp := n04bRootPhysicalChart_fst_pos hs
  rw [n04bRootDifferentialScale_abs hs, inv_pow, Real.sq_sqrt hp.le,
    inv_mul_cancel₀ (ne_of_gt hp)]

/-- Membership of the actual moving half supplies the positivity needed
by all the differential statements. -/
theorem n04bTravelHalfDomain_oriented_pos
    {Ω : Set PolarPoint} {F : PolarPoint → PolarPoint}
    {T : ℝ} {side : Bool} {x : PolarPoint}
    (hx : x ∈ n04bTravelHalfDomain Ω F T side) :
    0 < n04bTravelOrientation T side (F x).1 :=
  ((n04bTravelOrientation_mem_iff T side (F x).1).mp
    (mem_n04bTravelDomain.mp hx).2).1

end ContinuousFlexibility.Analysis
