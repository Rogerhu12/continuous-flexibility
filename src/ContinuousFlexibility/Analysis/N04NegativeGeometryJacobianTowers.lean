module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryHeightTowers
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Joint towers of the actual negative Jacobian and its reciprocal

The determinant is formed from the ordinary spatial differential of the
same stored chart. Fixed spatial jet evaluation identifies that differential
with its genuine joint parameter tower. Its nonzero component germ then
permits the absolute value and reciprocal on the original domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

theorem negativeChart_contDiffAt (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    ContDiffAt ℝ ∞
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side) p := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  exact (n04b_actualRootPhysical_regular_at W.through03 W.hS W.hT W.field
    hz' hs m side hp).1.congr_of_eventuallyEq
      ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
        hz' hs m side).component_chart_germ hp)

/-- Evaluating the actual spatial differential in one fixed direction
retains a genuine joint parameter and physical-point tower. -/
def negativeChartDerivativeJointTower (m : ℕ) (side : Bool) (v : PolarPoint) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        fderiv ℝ (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side) x.2 v) := by
  let J := W.negativeChartJointTower m side
  let JA := solveSmoothDirectionsPostcomp J (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let JB := solveSmoothDirectionsPostcomp J (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let KA := n04Realization_jointSpatialJet_directions JA 1 (fun _ => v)
  let KB := n04Realization_jointSpatialJet_directions JB 1 (fun _ => v)
  apply (smoothDirectionsProd KA KB).congrOn
  intro x hx
  have hF := (W.negativeChart_contDiffAt m side hx.1 hx.2).differentiableAt (by simp)
  simp only [iteratedFDeriv_one_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', fderiv.fst hF, fderiv.snd hF,
    ContinuousLinearMap.comp_apply, Prod.eta]

/-- The determinant is the polynomial in the two actual differential
columns, before taking an absolute value. -/
def negativeJacobianJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side) x.2) :=
  (smoothDirectionsProd (W.negativeChartDerivativeJointTower m side (1, 0))
    (W.negativeChartDerivativeJointTower m side (0, 1))).comp_contDiff isOpen_univ
    (((contDiff_fst.fst.mul contDiff_snd.snd).sub
      (contDiff_fst.snd.mul contDiff_snd.fst)) :
        ContDiff ℝ ∞ (fun q : PolarPoint × PolarPoint =>
          q.1.1 * q.2.2 - q.1.2 * q.2.1)).contDiffOn
    (fun _ _ => mem_univ _)

theorem negativeJacobian_ne_zero (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side) p ≠ 0 := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hg := (n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    hz' hs m side).component_chart_germ hp
  unfold planeJacobian
  rw [hg.fderiv_eq]
  exact (n04b_actualRootPhysical_regular_at W.through03 W.hS W.hT W.field
    hz' hs m side hp).2.2.1

def negativeAbsJacobianJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side) x.2|) :=
  (W.negativeJacobianJointTower m side).comp_contDiff
    (isOpen_ne_fun continuous_id continuous_const)
    (contDiffOn_id.abs (fun q (hq : q ≠ (0 : ℝ)) => hq))
    (fun x hx => W.negativeJacobian_ne_zero m side hx.1 hx.2)

def negativeJacobianInverseJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (W.C.left m) (W.C.right m) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side) x.2|⁻¹) :=
  (W.negativeAbsJacobianJointTower m side).comp_contDiff isOpen_Ioi
    (contDiffOn_id.inv (fun q (hq : q ∈ Ioi (0 : ℝ)) => hq.ne'))
    (fun x hx => abs_pos.mpr (W.negativeJacobian_ne_zero m side hx.1 hx.2))

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeJacobianInverseJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeJacobianInverseJointTower
