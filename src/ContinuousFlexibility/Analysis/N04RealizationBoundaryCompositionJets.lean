import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import ContinuousFlexibility.Scalar.WeightedTowerOperations

/-!
# Genuine composition jets at boundary points

The ordinary finite chain rule is applied at the actual points. Its
partition terms are assembled from genuine towers of the finite outer
operators and inner evaluations. Pointwise spatial smoothness suffices;
no common open smoothness extension is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X E F G : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set X} {f : X → F → G} {g : X → E → F} {p : X → E}

/-- Positive composition jets use only positive outer and inner jets. -/
def n04Realization_composedBoundaryJet_directions
    (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ (f x) (g x (p x)))
    (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ (g x) (p x))
    (n : ℕ) (hn : 0 < n)
    (JF : ∀ j, 1 ≤ j → j ≤ n →
      SmoothDirections U (fun x => iteratedFDeriv ℝ j (f x) (g x (p x))))
    (JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → E,
      SmoothDirections U (fun x => iteratedFDeriv ℝ j (g x) (p x) v))
    (v : Fin n → E) :
    SmoothDirections U (fun x => iteratedFDeriv ℝ n (f x ∘ g x) (p x) v) := by
  classical
  let term : OrderedFinpartition n → X → G := fun c x =>
    iteratedFDeriv ℝ c.length (f x) (g x (p x))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (g x) (p x) (v ∘ c.emb i))
  let JT (c : OrderedFinpartition n) : SmoothDirections U (term c) := by
    let Jtuple := smoothDirections_vectorTuple hU (fun i : Fin c.length =>
      JG (c.partSize i) (c.partSize_pos i) (c.partSize_le i) (v ∘ c.emb i))
    let Jpair := smoothDirectionsUniformProd
      (JF c.length (c.length_pos hn) c.length_le) Jtuple
    exact smoothDirections_contDiff_comp Jpair isOpen_univ
      (contDiff_multilinearEvaluation (Y := F) (Z := G) c.length).contDiffOn
      (fun _ _ => mem_univ _)
  let J := smoothDirections_finiteSum hU JT
  refine J.congr (fun x hx => ?_)
  change (∑ c, term c x) = iteratedFDeriv ℝ n (f x ∘ g x) (p x) v
  have he := congrArg (fun A : E [×n]→L[ℝ] G => A v)
    (iteratedFDeriv_comp (hf x hx) (hg x hx) (by simp : (n : ℕ∞ω) ≤ ∞))
  simpa only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, term] using he.symm

end ContinuousFlexibility.Analysis
