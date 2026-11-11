import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficients

/-!
# Exact divergence comparison for the return correction

This is the differential part of step 3 of the return-correction
construction. The coefficient identity is transferred through the
actual coordinate derivatives. Differentiability of the fluxes is
explicit; linearity of a totalized derivative on arbitrary functions
is never assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Two symmetric operators with the same radial coefficient differ
by precisely the divergence of their remaining coefficient errors. -/
theorem divergenceOperator_difference_same_radial
    (L K : SymmetricCoefficients) (hA : L.a = K.a) (u : PolarPoint → ℝ) (p : PolarPoint)
    (hLr : DifferentiableAt ℝ (symmetricNormalFlux L.a L.b u) p)
    (hKr : DifferentiableAt ℝ (symmetricNormalFlux K.a K.b u) p)
    (hLt : DifferentiableAt ℝ (symmetricAngularFlux L.b L.c u) p)
    (hKt : DifferentiableAt ℝ (symmetricAngularFlux K.b K.c u) p) :
    divergenceOperator L u p - divergenceOperator K u p =
      radialPartial (fun q => (L.b q - K.b q) * angularPartial u q) p +
      angularPartial (fun q => (L.b q - K.b q) * radialPartial u q +
        (L.c q - K.c q) * angularPartial u q) p := by
  have hrad : (fun q => (L.b q - K.b q) * angularPartial u q) =
      fun q => symmetricNormalFlux L.a L.b u q - symmetricNormalFlux K.a K.b u q := by
    funext q
    simp only [symmetricNormalFlux, hA]
    ring
  have hang : (fun q => (L.b q - K.b q) * radialPartial u q +
      (L.c q - K.c q) * angularPartial u q) =
      fun q => symmetricAngularFlux L.b L.c u q - symmetricAngularFlux K.b K.c u q := by
    funext q
    simp only [symmetricAngularFlux]
    ring
  rw [hrad, hang, radialPartial_sub hLr hKr, angularPartial_sub hLt hKt]
  simp only [divergenceOperator, symmetricNormalFlux, symmetricAngularFlux]
  ring

/-- Smooth coefficient and height germs supply the derivative
hypotheses of the exact comparison. -/
theorem divergenceOperator_difference_same_radial_of_contDiffAt
    (L K : SymmetricCoefficients) (hA : L.a = K.a) (u : PolarPoint → ℝ) (p : PolarPoint)
    (ha : ContDiffAt ℝ ∞ L.a p) (hb : ContDiffAt ℝ ∞ L.b p)
    (hc : ContDiffAt ℝ ∞ L.c p) (hkb : ContDiffAt ℝ ∞ K.b p)
    (hkc : ContDiffAt ℝ ∞ K.c p) (hu : ContDiffAt ℝ ∞ u p) :
    divergenceOperator L u p - divergenceOperator K u p =
      radialPartial (fun q => (L.b q - K.b q) * angularPartial u q) p +
      angularPartial (fun q => (L.b q - K.b q) * radialPartial u q +
        (L.c q - K.c q) * angularPartial u q) p := by
  have hka : ContDiffAt ℝ ∞ K.a p := hA ▸ ha
  exact divergenceOperator_difference_same_radial L K hA u p
    ((contDiffAt_symmetricNormalFlux ha hb hu).differentiableAt (by simp))
    ((contDiffAt_symmetricNormalFlux hka hkb hu).differentiableAt (by simp))
    ((contDiffAt_symmetricAngularFlux hb hc hu).differentiableAt (by simp))
    ((contDiffAt_symmetricAngularFlux hkb hkc hu).differentiableAt (by simp))

/-- The frozen linear coefficient error, evaluated at the actual
residual, is the exact operator difference after differentiation. -/
theorem returnCorrection_divergence_error
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a d v : PolarPoint → ℝ) (D V : PolarPoint → E →ₗ[ℝ] ℝ)
    (e : E) (u : PolarPoint → ℝ) (p : PolarPoint)
    (ha : ContDiffAt ℝ ∞ a p) (hd : ContDiffAt ℝ ∞ d p)
    (hv : ContDiffAt ℝ ∞ v p) (hD : ContDiffAt ℝ ∞ (fun q => D q e) p)
    (hV : ContDiffAt ℝ ∞ (fun q => V q e) p) (hu : ContDiffAt ℝ ∞ u p) :
    divergenceOperator (returnCorrectionCoefficients a d v) u p -
      divergenceOperator
        (returnCorrectionCoefficients a (fun q => d q + D q e) (fun q => v q + V q e)) u p =
      radialPartial (fun q =>
        (returnCoefficientError (a q) (d q) (v q) (D q) (V q) e e).1 * angularPartial u q) p +
      angularPartial (fun q =>
        (returnCoefficientError (a q) (d q) (v q) (D q) (V q) e e).1 * radialPartial u q +
        (returnCoefficientError (a q) (d q) (v q) (D q) (V q) e e).2 * angularPartial u q) p := by
  let L : SymmetricCoefficients := returnCorrectionCoefficients a d v
  let K : SymmetricCoefficients :=
    returnCorrectionCoefficients a (fun q => d q + D q e) (fun q => v q + V q e)
  have hA : L.a = K.a := by
    rw [returnCorrectionCoefficients_a, returnCorrectionCoefficients_a]
  have hcmp := divergenceOperator_difference_same_radial_of_contDiffAt L K hA u p
    ha (ha.mul hd) (ha.mul ((hd.pow 2).sub (hv.pow 2)))
    (ha.mul (hd.add hD))
    (ha.mul (((hd.add hD).pow 2).sub ((hv.add hV).pow 2))) hu
  have hb (q : PolarPoint) : L.b q - K.b q =
      (returnCoefficientError (a q) (d q) (v q) (D q) (V q) e e).1 :=
    (congrArg Prod.fst (returnCorrectionCoefficients_error_at_residual a d v D V e q)).symm
  have hc (q : PolarPoint) : L.c q - K.c q =
      (returnCoefficientError (a q) (d q) (v q) (D q) (V q) e e).2 :=
    (congrArg Prod.snd (returnCorrectionCoefficients_error_at_residual a d v D V e q)).symm
  simpa only [hb, hc] using hcmp

end ContinuousFlexibility.Statements
