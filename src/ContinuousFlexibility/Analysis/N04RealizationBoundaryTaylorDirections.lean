module

public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
public import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph
public import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative

/-!
# Genuine towers for the existing finite endpoint representative

The finite tuple contains the actual boundary coefficients at the same
angle. The fixed polynomial kernel reconstructs the original Taylor
formula on the entire plane, without assuming a tower for its output.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

def n04Realization_boundaryTaylor_jointDirections
    (hU : IsOpen U) (n : ℕ) (c : ℝ) (A : E → ℕ → ℝ → ℝ)
    (J : ∀ j : Fin (n + 1), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => A p.1 j p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => boundaryTaylorPolynomial n c (A p.1) p.2) := by
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
      (fun p : E × PolarPoint => fun j : Fin (n + 1) => A p.1 j p.2.2) :=
    ((smoothDirections_scalarTuple (hU.prod isOpen_univ) J).compLinear
      L hdomain hmap).congrOn (fun p _ => by
        funext j
        change A (L p).1 j (L p).2 = A p.1 j p.2.2
        rw [hL])
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JR : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.1) :=
    (smoothDirectionsLinearOn R hdomain).congrOn (fun _ _ => by
      simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  let K : (Fin (n + 1) → ℝ) × ℝ → ℝ := fun p =>
    ∑ j : Fin (n + 1), p.1 j / ((j : ℕ).factorial : ℝ) * (p.2 - c) ^ (j : ℕ)
  have hK : ContDiff ℝ ∞ K := by
    apply ContDiff.sum
    intro j _
    exact (((contDiff_apply ℝ ℝ j).comp contDiff_fst).div_const _).mul
      ((contDiff_snd.sub contDiff_const).pow (j : ℕ))
  let G := smoothDirectionsUniformProd JV JR
  apply (smoothDirections_contDiff_comp G isOpen_univ hK.contDiffOn
    (fun _ _ => mem_univ _)).congrOn
  intro p _
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => A p.1 j p.2.2 / (j.factorial : ℝ) * (p.2.1 - c) ^ j) (n + 1)

/-- In particular the representative uses the same actual radial jets. -/
def n04Realization_oneSidedRepresentative_jointDirections
    (hU : IsOpen U) (n : ℕ) (c : ℝ) (F : E → PolarPoint → ℝ)
    (J : ∀ j : Fin (n + 1), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (F p.1) c j p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => oneSidedBoundaryTaylorRepresentative n c (F p.1) p.2) :=
  n04Realization_boundaryTaylor_jointDirections hU n c
    (fun x => radialBoundaryJet (F x) c) J

end ContinuousFlexibility.Analysis
