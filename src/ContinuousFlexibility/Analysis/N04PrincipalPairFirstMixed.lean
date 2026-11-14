module

public import ContinuousFlexibility.Analysis.N04PrincipalPairAlgebra
public import ContinuousFlexibility.Scalar.WeightedPartialIdentities

/-!
# First mixed derivatives of paired families

The first ordinary mixed derivatives agree with the coordinate partials
of the same smooth current and reference fields. A nonempty parameter
domain supplies the reference spatial regularity already in the pair.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f : ι → X → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}

theorem firstMixed (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (hΩ : IsOpen Ω) (hU : U.Nonempty) (radial : Bool) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W
      (fun m x => mixedDerivative (if radial then 1 else 0) (if radial then 0 else 1) (f m x))
      (fun m => mixedDerivative (if radial then 1 else 0) (if radial then 0 else 1) (f₀ m)) := by
  obtain ⟨x₀, hx₀⟩ := hU
  cases radial
  · exact (hf.coordinatePartial hΩ false).congr hΩ
      (fun m x hx q hq => angularPartial_eq_mixedDerivative_on hΩ (hf.spatial m x hx) hq)
      (fun m q hq => angularPartial_eq_mixedDerivative_on hΩ
        (hf.reference_spatial m x₀ hx₀) hq)
  · exact (hf.coordinatePartial hΩ true).congr hΩ
      (fun m x hx q hq => radialPartial_eq_mixedDerivative_on hΩ (hf.spatial m x hx) hq)
      (fun m q hq => radialPartial_eq_mixedDerivative_on hΩ
        (hf.reference_spatial m x₀ hx₀) hq)

end N04PrincipalPairBounds

end ContinuousFlexibility.Analysis
