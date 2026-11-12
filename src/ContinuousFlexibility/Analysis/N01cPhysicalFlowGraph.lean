import ContinuousFlexibility.Analysis.N01cParameterCalculus
import ContinuousFlexibility.Analysis.N01cBoundsRestriction
import ContinuousFlexibility.Analysis.ProjectiveLimitSubspace
import ContinuousFlexibility.Scalar.WeightedTowerCompositionGeneric
import ContinuousFlexibility.Scalar.WeightedTowerOperations

/-!
# Genuine scalar composition along the state-flow graph

The existing projective composition theorem applies to the constant
real scale. Transport back by its continuous linear equivalence gives
the actual scalar tower, with its unchanged ordered-partition formula.
Pairing the state projection and the supplied flow yields the graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

section Composition

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {U : Set X} {V : Set Y} {f : X → Y} {g : Y → ℝ}

/-- Scalar-valued genuine composition through a locally convex state space. -/
def smoothDirections_realCompTVS
    (J : SmoothDirections U f) (K : SmoothDirections V g) (hmap : MapsTo f U V) :
    SmoothDirections U (g ∘ f) := by
  let e := constEquiv ℝ
  let KP := smoothDirections_postcompCLM K e.toContinuousLinearMap
  let CP := smoothDirectionsUniformCompGeneric J KP hmap
  let C := smoothDirections_postcompCLM CP e.symm.toContinuousLinearMap
  exact C.congr (fun x _ => e.symm_apply_apply (g (f x)))

theorem smoothDirections_realCompTVS_D_apply
    (J : SmoothDirections U f) (K : SmoothDirections V g) (hmap : MapsTo f U V)
    (n : ℕ) (x : X) (v : Fin n → X) :
    (smoothDirections_realCompTVS J K hmap).D n x v =
      ∑ c : OrderedFinpartition n,
        K.D c.length (f x) (fun i => J.D (c.partSize i) x (v ∘ c.emb i)) := by
  classical
  simp only [smoothDirections_realCompTVS, SmoothDirections.congr,
    smoothDirections_postcompCLM_D_apply, smoothDirectionsUniformCompGeneric_D,
    projectiveCompositionJets_apply, projectiveCompositionTerm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact (constEquiv ℝ).symm_apply_apply _

end Composition

section StateGraph

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {Θ : X × ℝ → ℝ}

/-- The first coordinate is the original state, and the second is the actual flow. -/
def smoothDirections_stateFlowGraph
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ) :
    SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => (p.1, Θ p)) :=
  smoothDirectionsUniformProd
    ((smoothDirectionsLinear (ContinuousLinearMap.fst ℝ X ℝ)).restrict
      J.open_domain (subset_univ _)) J

theorem smoothDirections_stateFlowGraph_D_apply
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (n : ℕ) (p : X × ℝ) (v : Fin n → X × ℝ) :
    (smoothDirections_stateFlowGraph J).D n p v =
      (continuousLinearJets (ContinuousLinearMap.fst ℝ X ℝ) n p v, J.D n p v) := by
  simp only [smoothDirections_stateFlowGraph, smoothDirectionsUniformProd,
    SmoothDirections.restrict, smoothDirectionsLinear, smoothDirectionsOfJets,
    ContinuousMultilinearMap.prod_apply]

theorem smoothDirections_stateFlowGraph_D_one
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (p : X × ℝ) (v : Fin 1 → X × ℝ) :
    (smoothDirections_stateFlowGraph J).D 1 p v = ((v 0).1, J.D 1 p v) := by
  simp only [smoothDirections_stateFlowGraph_D_apply, continuousLinearJets,
    ContinuousMultilinearMap.ofSubsingleton_apply_apply, ContinuousLinearMap.coe_fst']

theorem smoothDirections_stateFlowGraph_D_succ_succ
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (n : ℕ) (p : X × ℝ) (v : Fin (n + 2) → X × ℝ) :
    (smoothDirections_stateFlowGraph J).D (n + 2) p v = (0, J.D (n + 2) p v) := by
  simp only [smoothDirections_stateFlowGraph_D_apply, continuousLinearJets, zero_apply]

end StateGraph

end ContinuousFlexibility.Analysis
