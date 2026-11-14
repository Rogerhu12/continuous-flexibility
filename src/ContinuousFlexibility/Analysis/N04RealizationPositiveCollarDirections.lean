module

public import ContinuousFlexibility.Analysis.N04RealizationPositiveCollarKernel
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
public import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# The same radial collar on a topological state neighborhood

Only its finite actual boundary traces enter the smooth coefficient
kernel. The product of the state neighborhood with the full physical
plane is retained, including all collar endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

/-- Joint endpoint traces produce the literal integral collar. -/
def n04Realization_positiveCollar_jointDirections
    (hU : IsOpen U) (n : ℕ) (l r δ v m : ℝ) (root : Bool)
    (A : E → ℕ → ℝ → ℝ)
    (hA : ∀ x ∈ U, ∀ j ≤ n + 1, ContDiff ℝ ∞ (A x j))
    (J : ∀ j : Fin (n + 2), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => A p.1 j p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => positiveReferenceCollarCoordinate n l r δ v m root
        (A p.1) Prod.fst p.2) := by
  let L : (E × PolarPoint) →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hL (p : E × PolarPoint) : L p = (p.1, p.2.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hdomain : IsOpen (U ×ˢ (univ : Set PolarPoint)) := hU.prod isOpen_univ
  have hmap : MapsTo L (U ×ˢ univ) (U ×ˢ univ) := by
    intro p hp
    rw [hL]
    exact ⟨hp.1, mem_univ _⟩
  let JV : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => fun j : Fin (n + 2) => A p.1 j p.2.2) :=
    ((smoothDirections_scalarTuple (hU.prod isOpen_univ) J).compLinear
      L hdomain hmap).congrOn (fun p _ => by
        funext j
        change A (L p).1 j (L p).2 = A p.1 j p.2.2
        rw [hL])
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JR : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.1) :=
    (smoothDirectionsLinearOn R hdomain).congrOn (fun p _ => by
      simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  let G := smoothDirectionsUniformProd JV JR
  let K := smoothDirections_contDiff_comp G isOpen_univ
    (n04Realization_positiveCollarKernel_contDiff n l r δ v m root).contDiffOn
    (fun _ _ => mem_univ _)
  apply K.congr
  intro p hp
  change n04Realization_positiveCollarKernel n l r δ v m root
      ((fun j : Fin (n + 2) => A p.1 j p.2.2), p.2.1) = _
  exact (n04Realization_positiveCollarKernel_eq l r δ v m root
    (A p.1) (hA p.1 hp.1) p.2.1 p.2.2).symm

end ContinuousFlexibility.Analysis
