import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryFormulaDirections

/-!
# The actual finite even and odd root trace packet

The supplied root-coordinate witnesses need only satisfy their existing
pointwise transport properties. Their even traces through order four and
odd traces through order three are the fixed boundary formulas, so the
genuine input towers determine the actual output towers on the same set.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The finite packet requires no parameter regularity of the selected
root-flow witness itself. All normal orders are explicit. -/
def n04Realization_rootFiniteTrace_directions
    {U : Set X}
    (d c : X → PolarPoint → ℝ) (β : X → ℝ → ℝ)
    (Φ : X → ℝ → ℝ → ℝ) (R σ : X → ℝ) (G : X → ℝ × ℝ × ℝ → ℝ)
    (P : ∀ x ∈ U, N04bRootCoordinateProperties (d x) (c x) (β x)
      (Φ x) (R x) (σ x) (G x))
    (hd : ∀ x ∈ U, ContDiff ℝ ∞ (d x))
    (hc : ∀ x ∈ U, ContDiff ℝ ∞ (c x))
    (Jd : ∀ n : Fin 4, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (d p.1) 0 n.val p.2))
    (Jc : ∀ n : Fin 4, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (c p.1) 0 n.val p.2))
    (Jβ : SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p : X × ℝ => β p.1 p.2)) :
    (∀ n : Fin 5, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 n.val p.2)) ×
    (∀ n : Fin 4, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ =>
        radialBoundaryJet (extendedRootOddCoefficient (G p.1)) 0 n.val p.2)) := by
  let v : X → N06RootBoundaryInputs := fun x => n06RootBoundaryInputs (d x) (c x) (β x)
  let Jβ' := n04Realization_jointAngleDeriv_directions Jβ
  let Jv : ∀ i : Fin 9, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => v p.1 i p.2) :=
    Fin.cases (Jd 0) (Fin.cases (Jd 1) (Fin.cases (Jd 2) (Fin.cases (Jd 3)
      (Fin.cases (Jc 0) (Fin.cases (Jc 1) (Fin.cases (Jc 2)
        (Fin.cases (Jc 3) (Fin.cases Jβ' (fun i => i.elim0)))))))))
  let J := n04Realization_rootBoundaryFormula_directions v Jv
  have hformula (x : X) (hx : x ∈ U) :=
    (P x hx).n06_boundary_finite_formulas (hd x hx) (hc x hx)
  let E0 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 0 p.2) :=
    Jβ.congr (fun p hp => ((P p.1 hp.1).n06_even_boundary_jet_zero p.2).symm)
  let E1 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 1 p.2) :=
    J.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).1.symm)
  let E2 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 2 p.2) :=
    J.2.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.1.symm)
  let E3 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 3 p.2) :=
    J.2.2.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.2.1.symm)
  let E4 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootEven (G p.1)) 0 4 p.2) :=
    J.2.2.2.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.2.2.1.symm)
  let O0 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootOddCoefficient (G p.1)) 0 0 p.2) :=
    J.2.2.2.2.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.2.2.2.1.symm)
  let O1 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootOddCoefficient (G p.1)) 0 1 p.2) :=
    J.2.2.2.2.2.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.2.2.2.2.1.symm)
  let O2 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootOddCoefficient (G p.1)) 0 2 p.2) :=
    J.2.2.2.2.2.2.1.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.2.2.2.2.2.1.symm)
  let O3 : SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p : X × ℝ => radialBoundaryJet (extendedRootOddCoefficient (G p.1)) 0 3 p.2) :=
    J.2.2.2.2.2.2.2.congr (fun p hp => congrArg (fun f : ℝ → ℝ => f p.2)
      (hformula p.1 hp.1).2.2.2.2.2.2.2.symm)
  exact ⟨Fin.cases E0 (Fin.cases E1 (Fin.cases E2 (Fin.cases E3 (Fin.cases E4 (fun i => i.elim0))))),
    Fin.cases O0 (Fin.cases O1 (Fin.cases O2 (Fin.cases O3 (fun i => i.elim0))))⟩

end ContinuousFlexibility.Analysis
