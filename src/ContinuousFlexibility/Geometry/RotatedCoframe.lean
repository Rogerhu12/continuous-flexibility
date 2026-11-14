module

public import ContinuousFlexibility.Scalar.HeightDerivatives
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Rotating a planar coframe with exact connection

The two coordinate coefficients of a one-form are actual functions on
`PolarPoint`. Its exterior coefficient uses actual Frechet partials.
The Cartan equations are explicit premises of the general closure lemmas;
their verification for a particular remainder metric is a separate step.

This is the calculation in Section 2, lines 84--94: if the connection is
`dψ`, then `exp(iψ) (η₁ + iη₂)` is closed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A real one-form expressed in the two coordinate directions. -/
structure PlaneOneForm where
  radial : PolarPoint → ℝ
  angular : PolarPoint → ℝ

/-- The coefficient of `dr ∧ dθ` in a wedge of one-forms. -/
def wedgeCoefficient (η ξ : PlaneOneForm) (x : PolarPoint) : ℝ :=
  η.radial x * ξ.angular x - η.angular x * ξ.radial x

/-- The coefficient of `dr ∧ dθ` in the actual exterior derivative. -/
def exteriorCoefficient (η : PlaneOneForm) (x : PolarPoint) : ℝ :=
  radialPartial η.angular x - angularPartial η.radial x

/-- The coordinate differential of an actual scalar function. -/
def coordinateDifferential (ψ : PolarPoint → ℝ) : PlaneOneForm :=
  ⟨radialPartial ψ, angularPartial ψ⟩

/-- Evaluation of a one-form on a coordinate tangent vector. -/
def formValue (η : PlaneOneForm) (x v : PolarPoint) : ℝ :=
  η.radial x * v.1 + η.angular x * v.2

/-- The real part of `exp(iψ) (η₁ + iη₂)`. -/
def rotatedCoframeOne (ψ : PolarPoint → ℝ) (η₁ η₂ : PlaneOneForm) : PlaneOneForm :=
  ⟨fun x => Real.cos (ψ x) * η₁.radial x - Real.sin (ψ x) * η₂.radial x,
   fun x => Real.cos (ψ x) * η₁.angular x - Real.sin (ψ x) * η₂.angular x⟩

/-- The imaginary part of `exp(iψ) (η₁ + iη₂)`. -/
def rotatedCoframeTwo (ψ : PolarPoint → ℝ) (η₁ η₂ : PlaneOneForm) : PlaneOneForm :=
  ⟨fun x => Real.sin (ψ x) * η₁.radial x + Real.cos (ψ x) * η₂.radial x,
   fun x => Real.sin (ψ x) * η₁.angular x + Real.cos (ψ x) * η₂.angular x⟩

variable {ψ : PolarPoint → ℝ} {η₁ η₂ : PlaneOneForm} {x : PolarPoint}

theorem exteriorCoefficient_coordinateDifferential (hψ : ContDiffAt ℝ 2 ψ x) :
    exteriorCoefficient (coordinateDifferential ψ) x = 0 := by
  exact sub_eq_zero.mpr (radial_angular_commute hψ)

theorem contDiffAt_rotatedCoframeOne_radial {n : ℕ∞ω}
    (hψ : ContDiffAt ℝ n ψ x)
    (h1r : ContDiffAt ℝ n η₁.radial x) (h2r : ContDiffAt ℝ n η₂.radial x) :
    ContDiffAt ℝ n (rotatedCoframeOne ψ η₁ η₂).radial x :=
  (hψ.cos.mul h1r).sub (hψ.sin.mul h2r)

theorem contDiffAt_rotatedCoframeOne_angular {n : ℕ∞ω}
    (hψ : ContDiffAt ℝ n ψ x)
    (h1θ : ContDiffAt ℝ n η₁.angular x) (h2θ : ContDiffAt ℝ n η₂.angular x) :
    ContDiffAt ℝ n (rotatedCoframeOne ψ η₁ η₂).angular x :=
  (hψ.cos.mul h1θ).sub (hψ.sin.mul h2θ)

theorem contDiffAt_rotatedCoframeTwo_radial {n : ℕ∞ω}
    (hψ : ContDiffAt ℝ n ψ x)
    (h1r : ContDiffAt ℝ n η₁.radial x) (h2r : ContDiffAt ℝ n η₂.radial x) :
    ContDiffAt ℝ n (rotatedCoframeTwo ψ η₁ η₂).radial x :=
  (hψ.sin.mul h1r).add (hψ.cos.mul h2r)

theorem contDiffAt_rotatedCoframeTwo_angular {n : ℕ∞ω}
    (hψ : ContDiffAt ℝ n ψ x)
    (h1θ : ContDiffAt ℝ n η₁.angular x) (h2θ : ContDiffAt ℝ n η₂.angular x) :
    ContDiffAt ℝ n (rotatedCoframeTwo ψ η₁ η₂).angular x :=
  (hψ.sin.mul h1θ).add (hψ.cos.mul h2θ)

theorem radialPartial_cos (hψ : DifferentiableAt ℝ ψ x) :
    radialPartial (fun y => Real.cos (ψ y)) x =
      -Real.sin (ψ x) * radialPartial ψ x := by
  unfold radialPartial
  rw [hψ.hasFDerivAt.cos.fderiv]
  simp only [smul_apply, smul_eq_mul]

theorem angularPartial_cos (hψ : DifferentiableAt ℝ ψ x) :
    angularPartial (fun y => Real.cos (ψ y)) x =
      -Real.sin (ψ x) * angularPartial ψ x := by
  unfold angularPartial
  rw [hψ.hasFDerivAt.cos.fderiv]
  simp only [smul_apply, smul_eq_mul]

theorem radialPartial_sin (hψ : DifferentiableAt ℝ ψ x) :
    radialPartial (fun y => Real.sin (ψ y)) x =
      Real.cos (ψ x) * radialPartial ψ x := by
  unfold radialPartial
  rw [hψ.hasFDerivAt.sin.fderiv]
  simp only [smul_apply, smul_eq_mul]

theorem angularPartial_sin (hψ : DifferentiableAt ℝ ψ x) :
    angularPartial (fun y => Real.sin (ψ y)) x =
      Real.cos (ψ x) * angularPartial ψ x := by
  unfold angularPartial
  rw [hψ.hasFDerivAt.sin.fderiv]
  simp only [smul_apply, smul_eq_mul]

/-- Exterior differentiation of the first rotated form, before Cartan is used. -/
theorem exteriorCoefficient_rotatedCoframeOne
    (hψ : DifferentiableAt ℝ ψ x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x) :
    exteriorCoefficient (rotatedCoframeOne ψ η₁ η₂) x =
      Real.cos (ψ x) * exteriorCoefficient η₁ x -
        Real.sin (ψ x) * exteriorCoefficient η₂ x -
        Real.sin (ψ x) * wedgeCoefficient (coordinateDifferential ψ) η₁ x -
        Real.cos (ψ x) * wedgeCoefficient (coordinateDifferential ψ) η₂ x := by
  have hr := (hψ.hasFDerivAt.cos.mul h1r.hasFDerivAt).sub
    (hψ.hasFDerivAt.sin.mul h2r.hasFDerivAt)
  have hθ := (hψ.hasFDerivAt.cos.mul h1θ.hasFDerivAt).sub
    (hψ.hasFDerivAt.sin.mul h2θ.hasFDerivAt)
  change HasFDerivAt (rotatedCoframeOne ψ η₁ η₂).radial _ x at hr
  change HasFDerivAt (rotatedCoframeOne ψ η₁ η₂).angular _ x at hθ
  simp only [exteriorCoefficient, radialPartial, angularPartial]
  rw [hθ.fderiv, hr.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, wedgeCoefficient,
    coordinateDifferential, radialPartial, angularPartial]
  ring

/-- Exterior differentiation of the second rotated form, before Cartan is used. -/
theorem exteriorCoefficient_rotatedCoframeTwo
    (hψ : DifferentiableAt ℝ ψ x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x) :
    exteriorCoefficient (rotatedCoframeTwo ψ η₁ η₂) x =
      Real.sin (ψ x) * exteriorCoefficient η₁ x +
        Real.cos (ψ x) * exteriorCoefficient η₂ x +
        Real.cos (ψ x) * wedgeCoefficient (coordinateDifferential ψ) η₁ x -
        Real.sin (ψ x) * wedgeCoefficient (coordinateDifferential ψ) η₂ x := by
  have hr := (hψ.hasFDerivAt.sin.mul h1r.hasFDerivAt).add
    (hψ.hasFDerivAt.cos.mul h2r.hasFDerivAt)
  have hθ := (hψ.hasFDerivAt.sin.mul h1θ.hasFDerivAt).add
    (hψ.hasFDerivAt.cos.mul h2θ.hasFDerivAt)
  change HasFDerivAt (rotatedCoframeTwo ψ η₁ η₂).radial _ x at hr
  change HasFDerivAt (rotatedCoframeTwo ψ η₁ η₂).angular _ x at hθ
  simp only [exteriorCoefficient, radialPartial, angularPartial]
  rw [hθ.fderiv, hr.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, wedgeCoefficient,
    coordinateDifferential, radialPartial, angularPartial]
  ring

/-- Exact connection plus the actual Cartan equations makes the first form closed. -/
theorem rotatedCoframeOne_closed
    (hψ : DifferentiableAt ℝ ψ x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x)
    (hcartan1 : exteriorCoefficient η₁ x =
      wedgeCoefficient (coordinateDifferential ψ) η₂ x)
    (hcartan2 : exteriorCoefficient η₂ x =
      -wedgeCoefficient (coordinateDifferential ψ) η₁ x) :
    exteriorCoefficient (rotatedCoframeOne ψ η₁ η₂) x = 0 := by
  rw [exteriorCoefficient_rotatedCoframeOne hψ h1r h1θ h2r h2θ, hcartan1, hcartan2]
  ring

/-- Exact connection plus the actual Cartan equations makes the second form closed. -/
theorem rotatedCoframeTwo_closed
    (hψ : DifferentiableAt ℝ ψ x)
    (h1r : DifferentiableAt ℝ η₁.radial x) (h1θ : DifferentiableAt ℝ η₁.angular x)
    (h2r : DifferentiableAt ℝ η₂.radial x) (h2θ : DifferentiableAt ℝ η₂.angular x)
    (hcartan1 : exteriorCoefficient η₁ x =
      wedgeCoefficient (coordinateDifferential ψ) η₂ x)
    (hcartan2 : exteriorCoefficient η₂ x =
      -wedgeCoefficient (coordinateDifferential ψ) η₁ x) :
    exteriorCoefficient (rotatedCoframeTwo ψ η₁ η₂) x = 0 := by
  rw [exteriorCoefficient_rotatedCoframeTwo hψ h1r h1θ h2r h2θ, hcartan1, hcartan2]
  ring

/-- Rotation preserves the pointwise metric defined by a coframe. -/
theorem rotatedCoframe_square_sum (ψ : PolarPoint → ℝ) (η₁ η₂ : PlaneOneForm)
    (x v : PolarPoint) :
    formValue (rotatedCoframeOne ψ η₁ η₂) x v ^ 2 +
        formValue (rotatedCoframeTwo ψ η₁ η₂) x v ^ 2 =
      formValue η₁ x v ^ 2 + formValue η₂ x v ^ 2 := by
  simp only [formValue, rotatedCoframeOne, rotatedCoframeTwo]
  calc
    _ = (Real.sin (ψ x) ^ 2 + Real.cos (ψ x) ^ 2) *
        ((η₁.radial x * v.1 + η₁.angular x * v.2) ^ 2 +
          (η₂.radial x * v.1 + η₂.angular x * v.2) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

/-- The pointwise coframe determinant, including its orientation, is preserved. -/
theorem rotatedCoframe_wedge_eq (ψ : PolarPoint → ℝ) (η₁ η₂ : PlaneOneForm)
    (x : PolarPoint) :
    wedgeCoefficient (rotatedCoframeOne ψ η₁ η₂) (rotatedCoframeTwo ψ η₁ η₂) x =
      wedgeCoefficient η₁ η₂ x := by
  simp only [wedgeCoefficient, rotatedCoframeOne, rotatedCoframeTwo]
  calc
    _ = (Real.sin (ψ x) ^ 2 + Real.cos (ψ x) ^ 2) *
        (η₁.radial x * η₂.angular x - η₁.angular x * η₂.radial x) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem rotatedCoframe_wedge_ne_zero
    (h : wedgeCoefficient η₁ η₂ x ≠ 0) :
    wedgeCoefficient (rotatedCoframeOne ψ η₁ η₂) (rotatedCoframeTwo ψ η₁ η₂) x ≠ 0 := by
  rw [rotatedCoframe_wedge_eq]
  exact h

theorem rotatedCoframe_wedge_pos
    (h : 0 < wedgeCoefficient η₁ η₂ x) :
    0 < wedgeCoefficient (rotatedCoframeOne ψ η₁ η₂) (rotatedCoframeTwo ψ η₁ η₂) x := by
  rw [rotatedCoframe_wedge_eq]
  exact h

end ContinuousFlexibility
