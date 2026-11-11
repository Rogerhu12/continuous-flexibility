import ContinuousFlexibility.Statements.Scalar

/-!
# State derivative of the normalized height residual

The normalized equation is differentiated in its height unknown, with the small
parameter fixed.  For a nonzero parameter the chain-rule factor cancels the
normalizing denominator.  At parameter zero the first variation is linear in
the height direction.  The resulting genuine derivative is then identified
with the corrected divergence and its residual error.

Source: `paper/flexible-surface-readable/03-height-equation.tex`, lines 474–518.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The first variation is linear along an affine family of directions. -/
theorem polarResidualVariation_heightFamily_direction
    (w : ℝ → ℝ) (z : PolarPoint → ℝ) {u η : PolarPoint → ℝ}
    (hu : ContDiff ℝ ∞ u) (hη : ContDiff ℝ ∞ η)
    {x : PolarPoint} (hr : x.1 ≠ 0) (t : ℝ) :
    polarResidualVariation w z (heightFamily u η t) x =
      polarResidualVariation w z u x + t * polarResidualVariation w z η x := by
  unfold polarResidualVariation polarCurvatureNumeratorVariation polarDiscriminantVariation
  rw [radialPartial_heightRadial_heightFamily hu hη,
    radialPartial_heightAngular_heightFamily hu hη hr,
    angularPartial_heightAngular_heightFamily hu hη hr]
  simp only [heightRadial_heightFamily (hu.differentiable (by simp))
      (hη.differentiable (by simp)),
    heightAngular_heightFamily (hu.differentiable (by simp)) (hη.differentiable (by simp)),
    heightFamily, darbouxNumeratorVariation]
  ring

/-- The height-state derivative exists at every value of the normalizing
parameter, including zero, and is the true divergence at the actual height. -/
theorem hasDerivAt_normalizedHeightResidual_state
    {w : ℝ → ℝ} {z u η : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    (hu : ContDiff ℝ ∞ u) (hη : ContDiff ℝ ∞ η)
    (q : ℝ) {x : PolarPoint} (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w (heightFamily z u q) x) :
    HasDerivAt (fun t => normalizedHeightResidual w z (heightFamily u η t) q x)
      (heightLinearizedDivergence w (heightFamily z u q) η x) 0 := by
  by_cases hq : q = 0
  · subst q
    simp only [heightFamily_zero] at hD ⊢
    have heq : (fun t => normalizedHeightResidual w z (heightFamily u η t) 0 x) =
        (fun t => x.1 * polarResidualVariation w z u x +
          t * (x.1 * polarResidualVariation w z η x)) := by
      funext t
      rw [normalizedHeightResidual_zero,
        polarResidualVariation_heightFamily_direction w z hu hη hr]
      ring
    rw [heq, heightLinearizedDivergence_eq_variation hw hz hη hr hD]
    simpa only [one_mul, zero_add] using
      (hasDerivAt_const 0 (x.1 * polarResidualVariation w z u x)).add
        ((hasDerivAt_id 0).mul_const (x.1 * polarResidualVariation w z η x))
  · have hf := hasDerivAt_radialScaledResidual_divergence hw
      (contDiff_heightFamily hz hu q) hη hr hD
    have hf' : HasDerivAt
        (fun t => x.1 * polarCoordinateResidual w (heightFamily (heightFamily z u q) η t) x)
        (heightLinearizedDivergence w (heightFamily z u q) η x) (q * 0) := by
      simpa only [mul_zero] using hf
    have hscale : HasDerivAt (fun t : ℝ => q * t) q 0 := by
      simpa only [mul_one] using (hasDerivAt_id 0).const_mul q
    have hcomp := (hf'.comp 0 hscale).div_const q
    have hfamily (t : ℝ) : heightFamily z (heightFamily u η t) q =
        heightFamily (heightFamily z u q) η (q * t) := by
      funext y
      unfold heightFamily
      ring
    have heq : (fun t => normalizedHeightResidual w z (heightFamily u η t) q x) =
        (fun t => x.1 *
          polarCoordinateResidual w (heightFamily (heightFamily z u q) η (q * t)) x / q) := by
      funext t
      rw [normalizedHeightResidual_of_ne_zero w z (heightFamily u η t) x hq, hfamily]
    rw [heq]
    simpa only [Function.comp_def, mul_div_cancel_right₀ _ hq] using hcomp

namespace Statements

/-- The normalized height-state derivative is the fixed-type divergence plus
the manuscript's exact residual error, also when the parameter is zero. -/
theorem hasDerivAt_normalizedResidual_corrected
    {w h : ℝ → ℝ} {u η : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hu : ContDiff ℝ ∞ u) (hη : ContDiff ℝ ∞ η)
    (hhw : ∀ r, HasDerivAt h (w r) r) (q : ℝ) {x : PolarPoint}
    (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w (heightFamily (Radial.radialHeightField h) u q) x)
    (hQ : heightQ (profileEnergy w x)
      (heightRadial (heightFamily (Radial.radialHeightField h) u q) x)
      (angularPartial (heightAngular (heightFamily (Radial.radialHeightField h) u q)) x) ≠ 0) :
    HasDerivAt (fun t => normalizedResidual w h (heightFamily u η t) q x)
      (heightCorrectedDivergence w (heightFamily (Radial.radialHeightField h) u q) η x + q *
        scalarCorrectionError (polarTypeB w (heightFamily (Radial.radialHeightField h) u q))
          (normalizedResidual w h u q) η x) 0 := by
  have hh' := Radial.contDiff_radialHeightField hh
  have hd := hasDerivAt_normalizedHeightResidual_state hw hh' hu hη q hr hD
  have hzero (y : PolarPoint) :
      polarCoordinateResidual w (Radial.radialHeightField h) y = 0 :=
    Radial.polarCoordinateResidual_radialHeightField hhw
      (hw.contDiffAt.differentiableAt (by simp))
  by_cases hq : q = 0
  · subst q
    have hc : polarCorrectedC w (Radial.radialHeightField h) =
        polarLinearC w (Radial.radialHeightField h) := by
      funext y
      rw [polarCorrectedC_eq_residual_correction, hzero]
      simp only [mul_zero, zero_div, sub_zero]
    simpa only [normalizedResidual, heightFamily_zero, heightCorrectedDivergence, hc,
      heightLinearizedDivergence, zero_mul, add_zero] using hd
  · have hz := contDiff_heightFamily hh' hu q
    obtain ⟨_, hB, _, hC, hType, hR⟩ :=
      contDiffAt_heightLinearCoefficients hw.contDiffAt hz.contDiffAt hr hD hQ
    have hηr := contDiffAt_radialPartial (x := x) hη.contDiffAt (m := ∞) (by simp)
    have hηθ := contDiffAt_angularPartial (x := x) hη.contDiffAt (m := ∞) (by simp)
    have hflux : DifferentiableAt ℝ (fun y =>
        polarLinearB w (heightFamily (Radial.radialHeightField h) u q) y * radialPartial η y +
          polarCorrectedC w (heightFamily (Radial.radialHeightField h) u q) y *
            angularPartial η y) x :=
      ((hB.mul hηr).add (hC.mul hηθ)).differentiableAt (by simp)
    have hnorm : normalizedHeightResidual w (Radial.radialHeightField h) u q =
        (fun y => y.1 *
          polarCoordinateResidual w (heightFamily (Radial.radialHeightField h) u q) y / q) :=
      funext (fun y => normalizedHeightResidual_of_ne_zero w (Radial.radialHeightField h) u y hq)
    have herr : DifferentiableAt ℝ (fun y =>
        polarTypeB w (heightFamily (Radial.radialHeightField h) u q) y *
          normalizedHeightResidual w (Radial.radialHeightField h) u q y * angularPartial η y) x := by
      rw [hnorm]
      exact ((hType.mul ((contDiffAt_fst.mul hR).div_const q)).mul hηθ).differentiableAt (by simp)
    exact hd.congr_deriv
      (heightLinearizedDivergence_eq_corrected_normalized w (Radial.radialHeightField h) u η q
        hzero hflux herr)

end Statements

end ContinuousFlexibility
