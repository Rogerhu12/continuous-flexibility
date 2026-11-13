import ContinuousFlexibility.Analysis.SmoothDirectionsFixedLast
import ContinuousFlexibility.Analysis.N01cFiniteAffineJets

/-!
# Fixed spatial jet evaluations on an arbitrary open joint domain

A finite affine restriction recovers the actual ordinary spatial jets.
It is enough that the supplied joint tower is defined on an open set;
no product neighborhood or new convexity assumption is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private def fixedJetDirections
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {W : Set X} (n : ℕ) {f : X → ℝ}
    (J : SmoothDirections W f) (v : Fin n → X) :
    SmoothDirections W (fun x => J.D n x v) := by
  induction n generalizing f with
  | zero =>
      exact J.congr (fun x hx => by
        have hv : v = (Fin.elim0 : Fin 0 → X) := Subsingleton.elim _ _
        simpa only [hv] using (J.zero x hx).symm)
  | succ n ih =>
      let w : X := v (Fin.last n)
      let u : Fin n → X := fun i => v i.castSucc
      let K := ih (J.fixedLast w) u
      apply K.congr
      intro x hx
      rw [SmoothDirections.fixedLast_apply]
      apply congrArg (J.D (n + 1) x)
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Fin.snoc_last u w
      · exact Fin.snoc_castSucc u w j

/-- Evaluated ordinary spatial jets are genuine parameter functions on
the same joint domain, even when that domain is not a product. -/
def n04Realization_jointSpatialJet_directions
    {X E : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set (X × E)} {f : X × E → ℝ}
    (J : SmoothDirections W f) (n : ℕ) (v : Fin n → E) :
    SmoothDirections W
      (fun z => iteratedFDeriv ℝ n (fun p => f (z.1, p)) z.2 v) := by
  let L : E →L[ℝ] X × E :=
    (0 : E →L[ℝ] X).prod (ContinuousLinearMap.id ℝ E)
  let K := fixedJetDirections n J (fun i => (0, v i))
  apply K.congr
  intro z hz
  have hpoint : (z.1, (0 : E)) + L z.2 = z := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.id_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.eta]
  have hfun : (fun p : E => f ((z.1, (0 : E)) + L p)) =
      (fun p => f (z.1, p)) := by
    funext p
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.id_apply, Prod.mk_add_mk, add_zero, zero_add]
  have hdirs : (fun i => L (v i)) = (fun i => ((0 : X), v i)) := by
    funext i
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.id_apply]
  have h := smoothDirections_iteratedFDeriv_finiteAffine
    J (z.1, (0 : E)) L n (y := z.2) (by simpa only [hpoint] using hz) v
  simpa only [hpoint, hfun, hdirs] using h.symm

end ContinuousFlexibility.Analysis
