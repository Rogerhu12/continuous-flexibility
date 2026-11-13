import ContinuousFlexibility.Analysis.RootChartWithin
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.TameProductDirections
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# State jets commute with the two root projections

At a positive physical radius the even and odd divided projections are
fixed linear combinations of two evaluations. Their genuine parameter
jets are therefore the same projections of the input jets. This does not
construct a degree-one periodic extension of a positive-order state jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f g : E → ℝ}

private theorem projection_linear_jet
    (a b : ℝ) (J : SmoothDirections U f) (K : SmoothDirections U g)
    (L : SmoothDirections U (fun x => a * f x + b * g x))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    L.D n x v = a * J.D n x v + b * K.D n x v := by
  let A : (ℝ × ℝ) →L[ℝ] ℝ :=
    a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ
  let P : SmoothDirections U (fun x => a * f x + b * g x) :=
    (solveSmoothDirectionsPostcomp (smoothDirectionsProd J K) A).congrOn
      (fun x _ => by
        simp only [A, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul])
  have he := congrArg (fun B : E [×n]→L[ℝ] ℝ => B v) (L.unique P n x hx)
  exact he.trans (by
    simp only [P, SmoothDirections.congrOn, solveSmoothDirectionsPostcomp,
      smoothDirectionsProd, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousMultilinearMap.prod_apply, A, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul])

/-- The exact even projection commutes with every genuine state jet. -/
theorem n04NegativeChart_rootEven_stateJet
    {G : E → ℝ × ℝ × ℝ → ℝ}
    (J : ∀ q, SmoothDirections U (fun x => G x q)) (p : PolarPoint)
    (K : SmoothDirections U (fun x => rootEven (G x) p))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = rootEven (fun q => (J q).D n x v) p := by
  let qPos : ℝ × ℝ × ℝ := (p.1, p.1 ^ (3 / 2 : ℝ), p.2)
  let qNeg : ℝ × ℝ × ℝ := (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)
  let K' : SmoothDirections U (fun z => (1 / 2 : ℝ) * G z qPos + (1 / 2 : ℝ) * G z qNeg) :=
    K.congrOn (fun z _ => by simp only [rootEven, qPos, qNeg]; ring)
  have h := projection_linear_jet (1 / 2 : ℝ) (1 / 2 : ℝ) (J qPos) (J qNeg) K' n x hx v
  exact h.trans (by simp only [rootEven, qPos, qNeg]; ring)

/-- On the open physical half, the signed divided odd coefficient also
commutes with every state jet. Its spatial estimate loses only the one
input derivative already present in the root-composition theorem. -/
theorem n04NegativeChart_rootOddCoefficient_stateJet
    {G : E → ℝ × ℝ × ℝ → ℝ}
    (J : ∀ q, SmoothDirections U (fun x => G x q))
    (p : PolarPoint) (hp : p.1 ≠ 0)
    (K : SmoothDirections U (fun x => rootOddCoefficient (G x) p))
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = rootOddCoefficient (fun q => (J q).D n x v) p := by
  let qPos : ℝ × ℝ × ℝ := (p.1, p.1 ^ (3 / 2 : ℝ), p.2)
  let qNeg : ℝ × ℝ × ℝ := (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)
  let c : ℝ := (2 * p.1 ^ (3 / 2 : ℝ))⁻¹
  let K' : SmoothDirections U (fun z => (-c) * G z qPos + c * G z qNeg) :=
    K.congrOn (fun z _ => by
      simp only [rootOddCoefficient, rootOdd, if_neg hp, qPos, qNeg, c, div_eq_mul_inv]
      ring)
  have h := projection_linear_jet (-c) c (J qPos) (J qNeg) K' n x hx v
  exact h.trans (by
    simp only [rootOddCoefficient, rootOdd, if_neg hp, qPos, qNeg, c, div_eq_mul_inv]
    ring)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootOddCoefficient_stateJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootOddCoefficient_stateJet
