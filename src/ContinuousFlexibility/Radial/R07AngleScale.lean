import ContinuousFlexibility.Statements.RadialTargets

/-!
# Normalizing the matching states without changing their angle

The auxiliary cone fixes the incoming solution at its cut, whereas the
height-exclusion estimate normalizes the incoming state at the join. The
angle sine is unchanged by either nonzero rescaling. These lemmas transfer
the estimate back to the cut normalization in the public R07 statement.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

theorem radialAngleSine_symm (v w : ℝ × ℝ) :
    Statements.radialAngleSine v w = Statements.radialAngleSine w v := by
  unfold Statements.radialAngleSine
  rw [show w.1 * v.2 - w.2 * v.1 = -(v.1 * w.2 - v.2 * w.1) by ring,
    abs_neg, mul_comm (sqrt (w.1 ^ 2 + w.2 ^ 2))]

/-- Rescaling the first boundary state by a nonzero real number preserves
the angle, including when the other vector is zero. -/
theorem radialAngleSine_scale_left {c : ℝ} (hc : c ≠ 0) (v w : ℝ × ℝ) :
    Statements.radialAngleSine (c * v.1, c * v.2) w =
      Statements.radialAngleSine v w := by
  unfold Statements.radialAngleSine
  dsimp only
  rw [show c * v.1 * w.2 - c * v.2 * w.1 =
      c * (v.1 * w.2 - v.2 * w.1) by ring,
    abs_mul, show (c * v.1) ^ 2 + (c * v.2) ^ 2 =
      c ^ 2 * (v.1 ^ 2 + v.2 ^ 2) by ring,
    sqrt_mul (sq_nonneg c), sqrt_sq_eq_abs, mul_assoc,
    mul_div_mul_left _ _ (abs_ne_zero.mpr hc)]

/-- Rescaling the natural boundary state also preserves the angle. -/
theorem radialAngleSine_scale_right {c : ℝ} (hc : c ≠ 0) (v w : ℝ × ℝ) :
    Statements.radialAngleSine v (c * w.1, c * w.2) =
      Statements.radialAngleSine v w := by
  rw [radialAngleSine_symm, radialAngleSine_scale_left hc, radialAngleSine_symm]

/-- Both normalizations may be chosen independently. -/
theorem radialAngleSine_scale {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) (v w : ℝ × ℝ) :
    Statements.radialAngleSine (c * v.1, c * v.2) (d * w.1, d * w.2) =
      Statements.radialAngleSine v w := by
  rw [radialAngleSine_scale_left hc, radialAngleSine_scale_right hd]

/-- The physical state scales by exactly the same constant as the
homogeneous solution. -/
theorem radialState_const_mul (D : Statements.ReferenceData) (j : ℕ)
    (r scale c : ℝ) {u : ℝ → ℝ} (hu : DifferentiableAt ℝ u r) :
    Statements.radialState D j r scale (fun x => c * u x) =
      (c * (Statements.radialState D j r scale u).1,
       c * (Statements.radialState D j r scale u).2) := by
  have hd : deriv (fun x => c * u x) r = c * deriv u r :=
    (hu.hasDerivAt.const_mul c).deriv
  unfold Statements.radialState
  dsimp only
  rw [hd]
  apply Prod.ext <;> dsimp only <;> ring

/-- Cut-normalized and join-normalized solutions give the same public
matching angle. -/
theorem radialState_angle_const_mul (D : Statements.ReferenceData) (j : ℕ)
    (r scale : ℝ) {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0)
    {u v : ℝ → ℝ} (hu : DifferentiableAt ℝ u r) (hv : DifferentiableAt ℝ v r) :
    Statements.radialAngleSine
      (Statements.radialState D j r scale (fun x => c * u x))
      (Statements.radialState D j r scale (fun x => d * v x)) =
        Statements.radialAngleSine
          (Statements.radialState D j r scale u) (Statements.radialState D j r scale v) := by
  rw [radialState_const_mul D j r scale c hu, radialState_const_mul D j r scale d hv,
    radialAngleSine_scale hc hd]

end ContinuousFlexibility.Radial
