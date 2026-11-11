import ContinuousFlexibility.Analysis.ScalarJetSchwarz
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# A fixed last derivative is an actual smooth directional tower

Fixing the last slot of the next multilinear jet preserves the genuine
line recurrence. This supplies spatial derivatives of all parameter
jets while keeping their parameter slots in their original order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

private def fixedLastEvaluation (w : E) : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun L := L w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_fin_snoc (n : ℕ) (w : E) :
    Continuous (fun v : Fin n → E => Fin.snoc (α := fun _ : Fin (n + 1) => E) v w) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (continuous_const : Continuous (fun _ : Fin n → E => w))
  · simpa only [Fin.snoc_castSucc] using (continuous_apply j : Continuous (fun v : Fin n → E => v j))

def fixedLastContinuousMultilinear {n : ℕ} (A : E [×(n + 1)]→L[ℝ] ℝ) (w : E) :
    E [×n]→L[ℝ] ℝ where
  toMultilinearMap := (fixedLastEvaluation w).compMultilinearMap A.toMultilinearMap.curryRight
  cont := A.cont.comp (continuous_fin_snoc n w)

theorem fixedLastContinuousMultilinear_apply {n : ℕ}
    (A : E [×(n + 1)]→L[ℝ] ℝ) (w : E) (v : Fin n → E) :
    fixedLastContinuousMultilinear A w v = A (Fin.snoc v w) := rfl

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E → ℝ}

def SmoothDirections.fixedLast (J : SmoothDirections U f) (w : E) :
    SmoothDirections U (fun x => J.D 1 x (fun _ => w)) where
  open_domain := J.open_domain
  D n x := fixedLastContinuousMultilinear (J.D (n + 1) x) w
  zero x hx := by
    rw [fixedLastContinuousMultilinear_apply]
    apply congrArg (J.D 1 x)
    funext i
    fin_cases i
    rfl
  continuous n := by
    have hmap : Continuous (fun p : E × (Fin n → E) =>
        (p.1, Fin.snoc (α := fun _ : Fin (n + 1) => E) p.2 w)) :=
      continuous_fst.prodMk ((continuous_fin_snoc n w).comp continuous_snd)
    simpa only [fixedLastContinuousMultilinear_apply, Function.comp_def] using
      (J.continuous (n + 1)).comp hmap.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)
  derivative n x hx v u := by
    change HasProjectiveLineDerivAt (fun y => J.D (n + 1) y (Fin.snoc v w))
      (J.D (n + 2) x (Fin.snoc (Fin.cons u v) w)) x u
    rw [← Fin.cons_snoc_eq_snoc_cons]
    exact J.derivative (n + 1) x hx (Fin.snoc v w) u

theorem SmoothDirections.fixedLast_apply (J : SmoothDirections U f)
    (w : E) (n : ℕ) (x : E) (v : Fin n → E) :
    (J.fixedLast w).D n x v = J.D (n + 1) x (Fin.snoc v w) := rfl

theorem SmoothDirections.fixedLast_eq_cons (J : SmoothDirections U f)
    (hc : Convex ℝ U) (w : E) (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    (J.fixedLast w).D n x v = J.D (n + 1) x (Fin.cons w v) :=
  (J.cons_eq_snoc hc n x hx w v).symm

end ContinuousFlexibility.Analysis
