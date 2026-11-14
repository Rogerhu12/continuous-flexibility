module

public import Mathlib.Basic.Real.Basic

/-!
# Coordinate expressions for the height equation

These are pointwise expressions from Section 3 of the supplied manuscript,
not definitions of geometric curvature. Their relation to derivatives of a
smooth height and to the Riemannian curvature is a separate proof obligation.
-/

@[expose] public section

namespace ContinuousFlexibility

/-- The radial metric coefficient `E = 1 + w²`. -/
def radialEnergy (w : ℝ) : ℝ := 1 + w ^ 2

/-- The discriminant `D` of the remainder metric. -/
def heightDiscriminant (E k p : ℝ) : ℝ := E * (1 - p ^ 2) - k ^ 2

/-- Evaluation of `g - dz ⊗ dz` on the polar vector `(x,y)`. -/
def remainderQuadratic (r E k p x y : ℝ) : ℝ :=
  (E - k ^ 2) * x ^ 2 - 2 * r * k * p * x * y +
    r ^ 2 * (1 - p ^ 2) * y ^ 2

/-- Coordinate positive definiteness of the two-dimensional remainder metric. -/
def RemainderPositive (r E k p : ℝ) : Prop :=
  ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 → 0 < remainderQuadratic r E k p x y

/-- The numerator `Q` of the radial coefficient of the linearization. -/
def heightQ (E k pθ : ℝ) : ℝ := k + E * pθ

/-- The curvature numerator, before division by `r D^(3/2)`. -/
noncomputable def darbouxNumerator (r E Er k p kr pr pθ : ℝ) : ℝ :=
  heightQ E k pθ * kr - E * r * pr ^ 2 -
    Er / 2 * (1 - p ^ 2 + k * pθ)

end ContinuousFlexibility
