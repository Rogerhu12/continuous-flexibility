import ContinuousFlexibility.Analysis.SmoothDirectionsPermutationSymmetry
import ContinuousFlexibility.Analysis.JointMixedTameBounds

/-!
# Symmetry of actual mixed parameter multilinear maps

Permutation symmetry holds at every spatial point of the open domain.
Locality of ordinary mixed derivatives therefore preserves the same
symmetry after radial and angular differentiation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

/-- No symmetry is assumed of the algebraic multilinear map: it follows
from the genuine scalar tower and locality of the spatial derivatives. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.mixedParameterMultilinearMap_comp_perm
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x : E) (hx : x ∈ U) (p : PolarPoint) (hp : p ∈ V)
    (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    J.mixedParameterMultilinearMap hV n a b x hx p hp (v ∘ σ) =
      J.mixedParameterMultilinearMap hV n a b x hx p hp v := by
  rw [SmoothDirections.mixedParameterMultilinearMap_apply,
    SmoothDirections.mixedParameterMultilinearMap_apply]
  apply mixedDerivative_congr_on_open hV _ a b hp
  intro q hq
  exact J.comp_perm hc n (x, q) ⟨hx, hq⟩ (fun i => (v i, (0 : PolarPoint))) σ

end ContinuousFlexibility.Analysis
