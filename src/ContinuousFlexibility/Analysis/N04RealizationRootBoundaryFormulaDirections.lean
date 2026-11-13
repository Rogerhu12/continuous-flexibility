import ContinuousFlexibility.Analysis.N04RealizationJointSpatialEvaluation
import ContinuousFlexibility.Analysis.N06RootBoundaryFiniteFormulas
import ContinuousFlexibility.Analysis.N01cParameterCalculus

/-!
# Genuine towers for the existing finite root formulas

The eight expressions are the existing even and odd boundary formulas.
Their angular derivatives are genuine spatial derivatives of the joint
tower. Only finite sums, products and fixed scalar multiples are used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {W : Set (X × ℝ)}

/-- Differentiate an actual joint trace in its scalar angle coordinate. -/
def n04Realization_jointAngleDeriv_directions
    {f : X × ℝ → ℝ} (J : SmoothDirections W f) :
    SmoothDirections W
      (fun p => deriv (fun θ => f (p.1, θ)) p.2) := by
  apply (n04Realization_jointSpatialJet_directions J 1 (fun _ => 1)).congr
  intro p _
  rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_one]

private def negDirections {f : X × ℝ → ℝ} (J : SmoothDirections W f) :
    SmoothDirections W (fun p => -f p) :=
  (smoothDirections_realConstMul (-1) J).congr (fun p _ => neg_one_mul (f p))

private def subDirections {f g : X × ℝ → ℝ}
    (J : SmoothDirections W f) (K : SmoothDirections W g) :
    SmoothDirections W (fun p => f p - g p) :=
  (smoothDirectionsAdd J (negDirections K)).congr
    (fun p _ => (sub_eq_add_neg (f p) (g p)).symm)

/-- The genuine tower of the fixed finite boundary polynomial packet. -/
def n04Realization_rootBoundaryFormula_directions
    (v : X → N06RootBoundaryInputs)
    (J : ∀ i : Fin 9, SmoothDirections W (fun p => v p.1 i p.2)) :
    SmoothDirections W (fun p => n06RootEvenFormula1 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootEvenFormula2 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootEvenFormula3 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootEvenFormula4 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootOddFormula0 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootOddFormula1 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootOddFormula2 (v p.1) p.2) ×
    SmoothDirections W (fun p => n06RootOddFormula3 (v p.1) p.2) := by
  let E1 : SmoothDirections W (fun p => n06RootEvenFormula1 (v p.1) p.2) :=
    negDirections (smoothDirections_realMul (J 0) (J 8))
  let O0 : SmoothDirections W (fun p => n06RootOddFormula0 (v p.1) p.2) := by
    simpa only [n06RootOddFormula0, mul_assoc] using
      smoothDirections_realConstMul (2 / 3 : ℝ) (smoothDirections_realMul (J 4) (J 8))
  let DE1 := n04Realization_jointAngleDeriv_directions E1
  let DO0 := n04Realization_jointAngleDeriv_directions O0
  let E2 : SmoothDirections W (fun p => n06RootEvenFormula2 (v p.1) p.2) :=
    negDirections (smoothDirectionsAdd (smoothDirections_realMul (J 0) DE1)
      (smoothDirections_realMul (J 1) (J 8)))
  let O1 : SmoothDirections W (fun p => n06RootOddFormula1 (v p.1) p.2) :=
    smoothDirections_realConstMul (2 / 5 : ℝ)
      (subDirections
        (smoothDirectionsAdd (smoothDirections_realMul (J 4) DE1)
          (smoothDirections_realMul (J 5) (J 8)))
        (smoothDirections_realMul (J 0) DO0))
  let DE2 := n04Realization_jointAngleDeriv_directions E2
  let DO1 := n04Realization_jointAngleDeriv_directions O1
  let E3 : SmoothDirections W (fun p => n06RootEvenFormula3 (v p.1) p.2) :=
    smoothDirectionsAdd
      (negDirections (smoothDirectionsAdd
        (smoothDirectionsAdd (smoothDirections_realMul (J 0) DE2)
          (smoothDirections_realMul (smoothDirections_realConstMul 2 (J 1)) DE1))
        (smoothDirections_realMul (J 2) (J 8))))
      (smoothDirections_realMul (smoothDirections_realConstMul 2 (J 4)) DO0)
  let O2 : SmoothDirections W (fun p => n06RootOddFormula2 (v p.1) p.2) :=
    smoothDirections_realConstMul (2 / 7 : ℝ)
      (subDirections
        (smoothDirectionsAdd
          (smoothDirectionsAdd (smoothDirections_realMul (J 4) DE2)
            (smoothDirections_realMul (smoothDirections_realConstMul 2 (J 5)) DE1))
          (smoothDirections_realMul (J 6) (J 8)))
        (smoothDirections_realConstMul 2
          (smoothDirectionsAdd (smoothDirections_realMul (J 0) DO1)
            (smoothDirections_realMul (J 1) DO0))))
  let DE3 := n04Realization_jointAngleDeriv_directions E3
  let DO2 := n04Realization_jointAngleDeriv_directions O2
  let E4 : SmoothDirections W (fun p => n06RootEvenFormula4 (v p.1) p.2) :=
    smoothDirectionsAdd
      (negDirections (smoothDirectionsAdd
        (smoothDirectionsAdd
          (smoothDirectionsAdd (smoothDirections_realMul (J 0) DE3)
            (smoothDirections_realMul (smoothDirections_realConstMul 3 (J 1)) DE2))
          (smoothDirections_realMul (smoothDirections_realConstMul 3 (J 2)) DE1))
        (smoothDirections_realMul (J 3) (J 8))))
      (smoothDirections_realConstMul 6
        (smoothDirectionsAdd (smoothDirections_realMul (J 4) DO1)
          (smoothDirections_realMul (J 5) DO0)))
  let O3 : SmoothDirections W (fun p => n06RootOddFormula3 (v p.1) p.2) :=
    smoothDirections_realConstMul (2 / 9 : ℝ)
      (subDirections
        (smoothDirectionsAdd
          (smoothDirectionsAdd
            (smoothDirectionsAdd (smoothDirections_realMul (J 4) DE3)
              (smoothDirections_realMul (smoothDirections_realConstMul 3 (J 5)) DE2))
            (smoothDirections_realMul (smoothDirections_realConstMul 3 (J 6)) DE1))
          (smoothDirections_realMul (J 7) (J 8)))
        (smoothDirections_realConstMul 3
          (smoothDirectionsAdd
            (smoothDirectionsAdd (smoothDirections_realMul (J 0) DO2)
              (smoothDirections_realMul (smoothDirections_realConstMul 2 (J 1)) DO1))
            (smoothDirections_realMul (J 2) DO0))))
  exact ⟨E1, E2, E3, E4, O0, O1, O2, O3⟩

end ContinuousFlexibility.Analysis
