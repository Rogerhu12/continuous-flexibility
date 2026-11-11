import ContinuousFlexibility.Scalar.HeightVariation

/-!
# Removing the height parameter singularity

At a zero-residual base height, the genuine curvature numerator along
`z + q η` is exactly quadratic in `q`. Factoring it gives the removable
normalized residual and proves its actual smoothness in the real parameter.
This does not assert tame smoothness on the later weighted function spaces.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The quadratic term excludes the numerator's height-independent term. -/
def polarCurvatureNumeratorQuadratic (w : ℝ → ℝ) (η : PolarPoint → ℝ)
    (x : PolarPoint) : ℝ :=
  polarCurvatureNumerator w η x + radialPartial (profileEnergy w) x / 2

theorem polarResidual_zero_iff_numerator_zero
    (w : ℝ → ℝ) (z : PolarPoint → ℝ) {x : PolarPoint} (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x) :
    polarCoordinateResidual w z x = 0 ↔ polarCurvatureNumerator w z x = 0 := by
  simp [polarCoordinateResidual, div_eq_zero_iff, mul_eq_zero, hr,
    (inverseDThreeHalves_pos _ hD).ne']

theorem polarCurvatureNumerator_heightFamily
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0) (q : ℝ) :
    polarCurvatureNumerator w (heightFamily z η q) x =
      polarCurvatureNumerator w z x + q * polarCurvatureNumeratorVariation w z η x +
        q ^ 2 * polarCurvatureNumeratorQuadratic w η x := by
  simp only [polarCurvatureNumerator, polarCurvatureNumeratorVariation,
    polarCurvatureNumeratorQuadratic]
  rw [radialPartial_heightRadial_heightFamily hz hη,
    radialPartial_heightAngular_heightFamily hz hη hr,
    angularPartial_heightAngular_heightFamily hz hη hr]
  simp only [heightRadial_heightFamily
      (hz.differentiable (by simp)) (hη.differentiable (by simp)),
    heightAngular_heightFamily (hz.differentiable (by simp)) (hη.differentiable (by simp)),
    heightFamily,
    darbouxNumerator, darbouxNumeratorVariation, heightQ]
  ring

/-- The manuscript's normalized source, with its genuine derivative at zero. -/
def normalizedHeightResidual (w : ℝ → ℝ) (z η : PolarPoint → ℝ)
    (q : ℝ) (x : PolarPoint) : ℝ :=
  if q = 0 then x.1 * polarResidualVariation w z η x
  else x.1 * polarCoordinateResidual w (heightFamily z η q) x / q

@[simp] theorem normalizedHeightResidual_zero
    (w : ℝ → ℝ) (z η : PolarPoint → ℝ) (x : PolarPoint) :
    normalizedHeightResidual w z η 0 x = x.1 * polarResidualVariation w z η x := by
  simp [normalizedHeightResidual]

theorem normalizedHeightResidual_of_ne_zero
    (w : ℝ → ℝ) (z η : PolarPoint → ℝ) (x : PolarPoint) {q : ℝ} (hq : q ≠ 0) :
    normalizedHeightResidual w z η q x =
      x.1 * polarCoordinateResidual w (heightFamily z η q) x / q := by
  simp [normalizedHeightResidual, hq]

/-- Factoring the actual numerator removes the division by `q` everywhere. -/
theorem normalizedHeightResidual_eq_factored
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0)
    (hzero : polarCurvatureNumerator w z x = 0) (q : ℝ) :
    normalizedHeightResidual w z η q x =
      (polarCurvatureNumeratorVariation w z η x +
        q * polarCurvatureNumeratorQuadratic w η x) *
          inverseDThreeHalves (polarDiscriminant w (heightFamily z η q) x) := by
  by_cases hq : q = 0
  · subst q
    simp [normalizedHeightResidual, polarResidualVariation, hzero]
    field_simp [hr]
  · rw [normalizedHeightResidual_of_ne_zero w z η x hq]
    unfold polarCoordinateResidual
    rw [polarCurvatureNumerator_heightFamily w hz hη hr q, hzero]
    field_simp [hr, hq]
    ring

/-- The removable source is genuinely `C∞` in its real construction
parameter on the positive-discriminant domain, including parameter zero. -/
theorem contDiffAt_normalizedHeightResidual
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ} {x : PolarPoint} {q : ℝ}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0)
    (hzero : polarCurvatureNumerator w z x = 0)
    (hD : 0 < polarDiscriminant w (heightFamily z η q) x) :
    ContDiffAt ℝ ∞ (fun t => normalizedHeightResidual w z η t x) q := by
  have hk : ContDiff ℝ ∞ (fun t => heightRadial (heightFamily z η t) x) := by
    simp_rw [heightRadial_heightFamily (hz.differentiable (by simp))
      (hη.differentiable (by simp))]
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hp : ContDiff ℝ ∞ (fun t => heightAngular (heightFamily z η t) x) := by
    simp_rw [heightAngular_heightFamily (hz.differentiable (by simp))
      (hη.differentiable (by simp))]
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hd : ContDiff ℝ ∞ (fun t => polarDiscriminant w (heightFamily z η t) x) :=
    (contDiff_const.mul (contDiff_const.sub (hp.pow 2))).sub (hk.pow 2)
  have ht : ContDiffAt ℝ ∞
      (fun t => inverseDThreeHalves (polarDiscriminant w (heightFamily z η t) x)) q :=
    contDiffAt_const.div (hd.contDiffAt.mul (hd.contDiffAt.sqrt hD.ne'))
      (mul_ne_zero hD.ne' (Real.sqrt_pos.mpr hD).ne')
  have heq : (fun t => normalizedHeightResidual w z η t x) =
      (fun t => (polarCurvatureNumeratorVariation w z η x +
        t * polarCurvatureNumeratorQuadratic w η x) *
          inverseDThreeHalves (polarDiscriminant w (heightFamily z η t) x)) :=
    funext (normalizedHeightResidual_eq_factored w hz hη hr hzero)
  rw [heq]
  exact (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).mul ht

theorem contDiffAt_normalizedHeightResidual_of_residual_zero
    (w : ℝ → ℝ) {z η : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiff ℝ ∞ z) (hη : ContDiff ℝ ∞ η) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x) (hzero : polarCoordinateResidual w z x = 0) :
    ContDiffAt ℝ ∞ (fun q => normalizedHeightResidual w z η q x) 0 := by
  apply contDiffAt_normalizedHeightResidual w hz hη hr
    ((polarResidual_zero_iff_numerator_zero w z hr hD).mp hzero)
  simpa using hD

end ContinuousFlexibility
