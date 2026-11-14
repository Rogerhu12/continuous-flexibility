module

public import ContinuousFlexibility.Scalar.Definitions
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Actual derivatives in polar coordinate space

The coordinate space is a real product, restricted to positive radius in
the theorems which use polar expressions. These derivatives are the actual
Fréchet derivatives evaluated on coordinate directions, not independent jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

abbrev PolarPoint := ℝ × ℝ

/-- The actual radial partial derivative on coordinate space. -/
def radialPartial (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  fderiv ℝ f x (1, 0)

/-- The actual angular partial derivative on coordinate space. -/
def angularPartial (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  fderiv ℝ f x (0, 1)

/-- The manuscript's `k = z_r`, as a function. -/
def heightRadial (z : PolarPoint → ℝ) : PolarPoint → ℝ := radialPartial z

/-- The manuscript's `p = z_θ/r`, as a function. -/
def heightAngular (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  angularPartial z x / x.1

/-- The radial metric coefficient, lifted to polar coordinate space. -/
def profileEnergy (w : ℝ → ℝ) (x : PolarPoint) : ℝ := radialEnergy (w x.1)

/-- The remainder discriminant computed from an actual profile and height. -/
def polarDiscriminant (w : ℝ → ℝ) (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  heightDiscriminant (profileEnergy w x) (heightRadial z x) (heightAngular z x)

end ContinuousFlexibility
