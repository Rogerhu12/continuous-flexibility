import ContinuousFlexibility.Statements.Scalar
import ContinuousFlexibility.Radial.FourierModes
import Mathlib.Data.Finset.Interval

/-!
# The exact finite-angular obstruction target

This is the complete statement of Appendix `prop:obs-finite-square`.
The object with finite Fourier support is `z²`, not necessarily `z`.
The statement is a proposition definition; it is not an asserted theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

/-- The real Darboux numerator for an arbitrary positive metric
coefficient E. In particular E is not restricted to `1+w²`. -/
def arbitraryEnergyDarbouxNumerator (E : ℝ → ℝ) (z : PolarPoint → ℝ)
    (x : PolarPoint) : ℝ :=
  darbouxNumerator x.1 (E x.1) (deriv E x.1) (heightRadial z x) (heightAngular z x)
    (radialPartial (heightRadial z) x) (radialPartial (heightAngular z) x)
    (angularPartial (heightAngular z) x)

def IsRadialOn (I : Set ℝ) (z : PolarPoint → ℝ) : Prop :=
  ∀ r ∈ I, ∀ θ φ : ℝ, z (r, θ) = z (r, φ)

/-- The actual finite complex Fourier expansion and real symmetry. -/
def FiniteFourierSquareOn (I : Set ℝ) (z : PolarPoint → ℝ) : Prop :=
  ∃ (J : ℕ) (b : ℤ → ℝ → ℂ),
    (∀ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), ContDiffOn ℝ 2 (b j) I) ∧
    (∀ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), ∀ r ∈ I,
      b (-j) r = star (b j r)) ∧
    ∀ r ∈ I, ∀ θ : ℝ,
      ((z (r, θ) ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
          b j r * Complex.exp (Complex.I * ((j : ℂ) * (θ : ℂ)))

/-- X03: arbitrary C¹ positive E, real C² Darboux solution, finite
Fourier square and a genuinely nonempty open radial collar imply
radiality throughout the connected interval, including its endpoints.
The differential equation is imposed in the interior, where the ambient
derivatives agree with the within derivatives. Endpoint values are reached
by continuity rather than by assuming ambient differentiability there. -/
def X03Statement : Prop :=
  ∀ (I : Set ℝ) (E : ℝ → ℝ) (z : PolarPoint → ℝ),
    OrdConnected I → I ⊆ Ioi (0 : ℝ) →
    ContDiffOn ℝ 1 E I → (∀ r ∈ I, 0 < E r) →
    ContDiffOn ℝ 2 z (I ×ˢ (Set.univ : Set ℝ)) →
    (∀ x ∈ interior I ×ˢ (Set.univ : Set ℝ), arbitraryEnergyDarbouxNumerator E z x = 0) →
    FiniteFourierSquareOn I z →
    (∃ J : Set ℝ, IsOpen J ∧ J.Nonempty ∧ J ⊆ I ∧ IsRadialOn J z) →
    IsRadialOn I z

end ContinuousFlexibility.Statements
