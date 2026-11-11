import ContinuousFlexibility.Radial.ModeTestIntegrability
import ContinuousFlexibility.Radial.RadialGreenBoundary

/-!
# From the actual differential expression to the frozen weak equation

The profile's flat endpoints annihilate the boundary Wronskian. A
globally smooth lift therefore satisfies the exact modal weak equation
on every region where its pointwise source equation holds. The test
condition is the ordinary support condition in the frozen definition.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matchingJacobi_continuousOn {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (j : ℕ) :
    ContinuousOn (radialJacobi ((j : ℝ) ^ 2) D.w u) (Icc D.a D.b) := by
  have hg := matchingProfileGeometry hD
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hddu := (contDiff_infty_iff_deriv.mp hdu).2
  have hratio : ContinuousOn (fun r : ℝ => (j : ℝ) ^ 2 / r) (Icc D.a D.b) := by
    apply continuous_const.continuousOn.div continuous_id.continuousOn
    intro r hr
    exact (lt_of_lt_of_le hg.1 hr.1).ne'
  have hc := (hw.continuous.continuousOn.mul hddu.continuous.continuousOn).add
    (hdw.continuous.continuousOn.mul
      (hdu.continuous.continuousOn.sub (hratio.mul hu.continuous.continuousOn)))
  apply hc.congr
  intro r _
  exact matchingJacobi_expansion hD hu j r

/-- The actual ordinary-radial Green identity for two smooth functions.
No boundary condition on either function is needed because the profile
itself vanishes at both ends. -/
theorem matchingJacobi_symmetric_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (j : ℕ) :
    (∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w v r) =
      ∫ r in D.a..D.b, v r * radialJacobi ((j : ℝ) ^ 2) D.w u r := by
  have hg := matchingProfileGeometry hD
  have hw := hg.2.2.1.1
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdv := (contDiff_infty_iff_deriv.mp hv).2
  have huv : IntervalIntegrable
      (fun r => u r * radialJacobi ((j : ℝ) ^ 2) D.w v r) volume D.a D.b :=
    (show ContinuousOn (fun r => u r * radialJacobi ((j : ℝ) ^ 2) D.w v r)
      (uIcc D.a D.b) by
        simpa only [uIcc_of_le hg.2.1.le] using
          hu.continuous.continuousOn.mul (matchingJacobi_continuousOn hD hv j)).intervalIntegrable
  have hvu : IntervalIntegrable
      (fun r => v r * radialJacobi ((j : ℝ) ^ 2) D.w u r) volume D.a D.b :=
    (show ContinuousOn (fun r => v r * radialJacobi ((j : ℝ) ^ 2) D.w u r)
      (uIcc D.a D.b) by
        simpa only [uIcc_of_le hg.2.1.le] using
          hv.continuous.continuousOn.mul (matchingJacobi_continuousOn hD hu j)).intervalIntegrable
  have hreg : ∀ r ∈ uIcc D.a D.b,
      DifferentiableAt ℝ D.w r ∧ DifferentiableAt ℝ u r ∧
      DifferentiableAt ℝ (deriv u) r ∧ DifferentiableAt ℝ v r ∧
      DifferentiableAt ℝ (deriv v) r := by
    intro r _
    exact ⟨hw.differentiable (by simp) r, hu.differentiable (by simp) r,
      hdu.differentiable (by simp) r, hv.differentiable (by simp) r,
      hdv.differentiable (by simp) r⟩
  have hgreen := integral_radialJacobi_green hreg (huv.sub hvu)
  have hwa : D.w D.a = 0 := hg.2.2.1.2 D.a (Or.inl le_rfl)
  have hwb : D.w D.b = 0 := hg.2.2.1.2 D.b (Or.inr le_rfl)
  rw [intervalIntegral.integral_sub huv hvu] at hgreen
  simp only [radialWronskian, hwa, hwb, zero_mul, sub_zero] at hgreen
  exact sub_eq_zero.mp hgreen

/-- A smooth actual representative and its actual pointwise weighted
source give the frozen weak modal equation on any test region. -/
theorem modeLocalEquation_of_smooth_pointwise {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {j : ℕ} {J : Set ℝ}
    {U F : RadialModePair D} {u f : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hU : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hF : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] f)
    (hscalar : U.2 = 0)
    (heq : ∀ r ∈ J, radialJacobi ((j : ℝ) ^ 2) D.w u r =
      -(12 * D.w r / r ^ 2) * f r) :
    ModeLocalEquation D j J U F := by
  intro ψ hψ _ hsupp
  rw [hscalar, zero_mul, sub_zero]
  calc
    (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
        ∫ r in D.a..D.b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
      apply matchingInterval_congr_ae hD
      filter_upwards [hU] with r hr
      rw [hr]
    _ = ∫ r in D.a..D.b, ψ r * radialJacobi ((j : ℝ) ^ 2) D.w u r :=
      matchingJacobi_symmetric_integral hD hu hψ j
    _ = -(∫ r in D.a..D.b, (12 * D.w r / r ^ 2) * F.1 r * ψ r) := by
      rw [← intervalIntegral.integral_neg]
      apply matchingInterval_congr_ae hD
      filter_upwards [hF] with r hr
      by_cases hz : ψ r = 0
      · simp only [hz, zero_mul, mul_zero, neg_zero]
      · rw [heq r (hsupp hz), hr]
        ring

end ContinuousFlexibility.Radial
