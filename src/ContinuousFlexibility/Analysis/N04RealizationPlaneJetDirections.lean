import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Scalar.WeightedTowerOperations
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Parameter towers of the actual plane multilinear maps

The two coordinate evaluations recover an existing plane linear map.
Currying repeats this finite reconstruction for an existing multilinear
map. Only genuine towers of its fixed-vector evaluations are inputs; no
new representation of a spatial jet is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set X}

/-- The coordinate evaluations determine the same plane operator. -/
def n04Realization_planeLinear_directions
    (A : X → PolarPoint →L[ℝ] Y)
    (Jr : SmoothDirections U (fun x => A x (1, 0)))
    (Jθ : SmoothDirections U (fun x => A x (0, 1))) :
    SmoothDirections U A := by
  let L : Y →L[ℝ] (PolarPoint →L[ℝ] Y) :=
    ContinuousLinearMap.smulRightL ℝ PolarPoint Y (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let R : Y →L[ℝ] (PolarPoint →L[ℝ] Y) :=
    ContinuousLinearMap.smulRightL ℝ PolarPoint Y (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let S : (Y × Y) →L[ℝ] (PolarPoint →L[ℝ] Y) :=
    L.comp (ContinuousLinearMap.fst ℝ Y Y) +
      R.comp (ContinuousLinearMap.snd ℝ Y Y)
  let J := solveSmoothDirectionsPostcomp (smoothDirectionsUniformProd Jr Jθ) S
  refine J.congr (fun x _ => ?_)
  ext v
  simp only [S, L, R, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  calc
    _ = A x (v.1 • ((1, 0) : PolarPoint) + v.2 • ((0, 1) : PolarPoint)) := by
      rw [map_add, map_smul, map_smul]
    _ = A x v := congrArg (A x) (by ext <;> simp)

/-- Finite currying upgrades fixed-vector towers to the actual operator
tower. The parameter domain and every spatial jet remain unchanged. -/
def n04Realization_planeMultilinear_directions
    (n : ℕ) (A : X → PolarPoint [×n]→L[ℝ] Y)
    (J : ∀ v : Fin n → PolarPoint, SmoothDirections U (fun x => A x v)) :
    SmoothDirections U A := by
  induction n generalizing A with
  | zero =>
      let e := continuousMultilinearCurryFin0 ℝ PolarPoint Y
      let K := solveSmoothDirectionsPostcomp (J (0 : Fin 0 → PolarPoint))
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap
      refine K.congr (fun x _ => ?_)
      ext v
      simp only [e, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, continuousMultilinearCurryFin0_symm_apply_apply]
      exact congrArg (A x) (Subsingleton.elim _ _)
  | succ n ih =>
      let B : X → PolarPoint →L[ℝ] (PolarPoint [×n]→L[ℝ] Y) :=
        fun x => (A x).curryLeft
      let JB (d : PolarPoint) : SmoothDirections U (fun x => B x d) :=
        ih (fun x => B x d) (fun v =>
          (J (Fin.cons d v)).congr (fun x _ => by
            simp only [B, ContinuousMultilinearMap.curryLeft_apply]))
      let K := n04Realization_planeLinear_directions B (JB (1, 0)) (JB (0, 1))
      let e := continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => PolarPoint) Y
      let K' := solveSmoothDirectionsPostcomp K
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap
      refine K'.congr (fun x _ => ?_)
      ext v
      simp only [e, B, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, continuousMultilinearCurryLeftEquiv_symm_apply,
        ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]

end ContinuousFlexibility.Analysis
