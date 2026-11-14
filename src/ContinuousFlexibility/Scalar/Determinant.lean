module

public import ContinuousFlexibility.Scalar.Definitions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Algebra of the linearized height equation

This file proves the pointwise algebra behind Section 3, equations
`eq:cart-determinant-identity` and
`eq:cart-completed-normalized-derivative` of the supplied manuscript.

The residual below is the explicit coordinate expression. Identifying it
with geometric curvature, and identifying these coefficients with the
derivative of the curvature residual, remain separate obligations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

/-- The factor `D^(-3/2)`, written without a real-power convention. -/
noncomputable def inverseDThreeHalves (D : ℝ) : ℝ := 1 / (D * Real.sqrt D)

/-- The radial coefficient of the symmetric linearized expression. -/
def linearRadial (E k pθ t : ℝ) : ℝ := heightQ E k pθ * t

/-- The mixed coefficient of the symmetric linearized expression. -/
def linearMixed (E pr t : ℝ) : ℝ := -E * pr * t

/-- The angular coefficient of the symmetric linearized expression. -/
def linearAngular (r E Er k kr t : ℝ) : ℝ :=
  (E * kr - Er * k / 2) * t / r

/-- The explicit coordinate residual with an arbitrary common scale factor. -/
def scaledCoordinateResidual (r E Er k p kr pr pθ t : ℝ) : ℝ :=
  darbouxNumerator r E Er k p kr pr pθ * t / r

/-- The type correction changes only the angular coefficient. -/
def correctedAngular (r E Er k p kr pr pθ t : ℝ) : ℝ :=
  linearAngular r E Er k kr t -
    E * scaledCoordinateResidual r E Er k p kr pr pθ t / heightQ E k pθ

/-- The shortened correction agrees with the manuscript's `B r N` formula. -/
theorem correctedAngular_eq_residual_correction
    (r E Er k p kr pr pθ t : ℝ)
    (hr : r ≠ 0) (hQ : heightQ E k pθ ≠ 0) :
    correctedAngular r E Er k p kr pr pθ t =
      linearAngular r E Er k kr t -
        (E / (r * heightQ E k pθ)) * r *
          scaledCoordinateResidual r E Er k p kr pr pθ t := by
  unfold correctedAngular
  field_simp [hr, hQ]

/-- At a zero of the residual the corrected and original coefficients agree. -/
theorem correctedAngular_of_residual_zero
    (r E Er k p kr pr pθ t : ℝ)
    (hres : scaledCoordinateResidual r E Er k p kr pr pθ t = 0) :
    correctedAngular r E Er k p kr pr pθ t = linearAngular r E Er k kr t := by
  simp [correctedAngular, hres]

/-- The numerator relation used in the manuscript's determinant calculation. -/
theorem heightQ_discriminant_identity (E k p pθ : ℝ) :
    k * heightQ E k pθ + heightDiscriminant E k p =
      E * (1 - p ^ 2 + k * pθ) := by
  unfold heightQ heightDiscriminant
  ring

/-- Determinant identity before imposing the square-root scale factor. -/
theorem linear_determinant_scaled
    (r E Er k p kr pr pθ t : ℝ) (hr : r ≠ 0) :
    linearRadial E k pθ t * linearAngular r E Er k kr t -
        linearMixed E pr t ^ 2 =
      (E * darbouxNumerator r E Er k p kr pr pθ +
        Er * heightDiscriminant E k p / 2) * t ^ 2 / r := by
  unfold linearRadial linearAngular linearMixed darbouxNumerator
    heightQ heightDiscriminant
  field_simp [hr]
  ring

/-- Squaring the square-root scale gives `D⁻³` on the positive domain. -/
theorem inverseDThreeHalves_sq (D : ℝ) (hD : 0 < D) :
    inverseDThreeHalves D ^ 2 = 1 / D ^ 3 := by
  unfold inverseDThreeHalves
  rw [div_pow, one_pow, mul_pow, Real.sq_sqrt (le_of_lt hD)]
  congr 1

/-- The square-root normalization is positive on its admissible domain. -/
theorem inverseDThreeHalves_pos (D : ℝ) (hD : 0 < D) :
    0 < inverseDThreeHalves D := by
  unfold inverseDThreeHalves
  exact one_div_pos.mpr (mul_pos hD (Real.sqrt_pos.mpr hD))

/-- The factor appearing in the curvature part of the determinant. -/
theorem discriminant_mul_inverseDThreeHalves_sq
    (D : ℝ) (hD : 0 < D) :
    D * inverseDThreeHalves D ^ 2 = 1 / D ^ 2 := by
  rw [inverseDThreeHalves_sq D hD]
  field_simp [ne_of_gt hD]

/-- The manuscript's determinant identity, for the coordinate residual.

Here `E' = 2 w w'`; no geometric interpretation of the coordinate residual
is assumed or asserted by this pointwise identity.
-/
theorem linear_determinant
    (r E w wr k p kr pr pθ : ℝ)
    (hr : r ≠ 0) (hD : 0 < heightDiscriminant E k p) :
    let D := heightDiscriminant E k p
    let t := inverseDThreeHalves D
    linearRadial E k pθ t * linearAngular r E (2 * w * wr) k kr t -
        linearMixed E pr t ^ 2 =
      (w * wr / r) / D ^ 2 +
        E * t * scaledCoordinateResidual r E (2 * w * wr) k p kr pr pθ t := by
  dsimp only
  rw [linear_determinant_scaled r E (2 * w * wr) k p kr pr pθ _ hr]
  calc
    _ = E * inverseDThreeHalves (heightDiscriminant E k p) *
          scaledCoordinateResidual r E (2 * w * wr) k p kr pr pθ
            (inverseDThreeHalves (heightDiscriminant E k p)) +
        (w * wr / r) *
          (heightDiscriminant E k p * inverseDThreeHalves (heightDiscriminant E k p) ^ 2) := by
      unfold scaledCoordinateResidual
      field_simp [hr]
    _ = _ := by
      rw [discriminant_mul_inverseDThreeHalves_sq _ hD]
      ring

/-- The residual correction removes the residual term in the determinant. -/
theorem corrected_determinant_scaled
    (r E Er k p kr pr pθ t : ℝ)
    (hr : r ≠ 0) (hQ : heightQ E k pθ ≠ 0) :
    linearRadial E k pθ t * correctedAngular r E Er k p kr pr pθ t -
        linearMixed E pr t ^ 2 =
      Er * heightDiscriminant E k p * t ^ 2 / (2 * r) := by
  unfold correctedAngular linearRadial linearAngular linearMixed
    scaledCoordinateResidual darbouxNumerator heightDiscriminant
  field_simp [hr, hQ]
  simp only [heightQ]
  ring

/-- On the positive discriminant domain the corrected determinant is exactly
the reference coefficient `K₀ = w w' / r` divided by `D²`. -/
theorem corrected_determinant
    (r E w wr k p kr pr pθ : ℝ)
    (hr : r ≠ 0) (hD : 0 < heightDiscriminant E k p)
    (hQ : heightQ E k pθ ≠ 0) :
    let D := heightDiscriminant E k p
    let t := inverseDThreeHalves D
    linearRadial E k pθ t * correctedAngular r E (2 * w * wr) k p kr pr pθ t -
        linearMixed E pr t ^ 2 =
      (w * wr / r) / D ^ 2 := by
  dsimp only
  rw [corrected_determinant_scaled r E (2 * w * wr) k p kr pr pθ _ hr hQ]
  rw [inverseDThreeHalves_sq _ hD]
  field_simp [hr, ne_of_gt hD]

/-- At the radial reference height the discriminant is exactly one. -/
theorem heightDiscriminant_radial (w : ℝ) :
    heightDiscriminant (radialEnergy w) w 0 = 1 := by
  unfold heightDiscriminant radialEnergy
  ring

/-- The normalization factor equals one at the radial reference height. -/
theorem inverseDThreeHalves_one : inverseDThreeHalves 1 = 1 := by
  simp [inverseDThreeHalves]

/-- Pointwise specialization of the three coefficients at `z = h`.

The jets supplied here are `k = w`, `p = pθ = pr = 0`, `kr = wr`,
and `Er = 2 w wr`. Connecting them to a height function is not needed
for this algebraic specialization.
-/
theorem radial_linear_coefficients (r w wr : ℝ) :
    let E := radialEnergy w
    let t := inverseDThreeHalves (heightDiscriminant E w 0)
    linearRadial E w 0 t = w ∧
      linearMixed E 0 t = 0 ∧
      linearAngular r E (2 * w * wr) w wr t = wr / r := by
  dsimp only
  simp only [heightDiscriminant_radial, inverseDThreeHalves_one]
  constructor
  · simp [linearRadial, heightQ]
  constructor
  · simp [linearMixed]
  · unfold linearAngular radialEnergy
    apply congrArg (fun v : ℝ => v / r)
    ring

/-- The explicit coordinate residual vanishes on the radial reference jets. -/
theorem radial_coordinate_residual_zero (r w wr t : ℝ) :
    scaledCoordinateResidual r (radialEnergy w) (2 * w * wr)
      w 0 wr 0 0 t = 0 := by
  unfold scaledCoordinateResidual
  have hnum : darbouxNumerator r (radialEnergy w) (2 * w * wr)
      w 0 wr 0 0 = 0 := by
    unfold darbouxNumerator heightQ radialEnergy
    ring
  rw [hnum]
  simp

end ContinuousFlexibility
