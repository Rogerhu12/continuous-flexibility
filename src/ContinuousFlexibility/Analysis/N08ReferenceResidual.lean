import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Radial.R11bFourierTests

/-!
# The actual scalar residual at the reference state

The reference controls and metric parameter vanish.  Its profile is
therefore exactly the radial reference profile, and the removable value
at `q = 0` is its Jacobi operator applied to the distinguished second
mode.  The reference kernel equation proves that this residual vanishes.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

theorem n08_stateKappa_reference
    (href : referenceStateConditions D S C) (m : ℕ) :
    stateKappa S C.referenceState m = 0 := by
  simp only [stateKappa, href.2.2.2.1, map_zero, Pi.zero_apply,
    angularMean, intervalIntegral.integral_zero, mul_zero]

theorem n08_stateProfile_reference
    (href : referenceStateConditions D S C) :
    stateProfile D S C C.referenceState = D.w := by
  funext r
  simp only [stateProfile, href.2.2.1, n08_stateKappa_reference href,
    zero_mul, tsum_zero, zero_add, Real.exp_zero, mul_one]

theorem n08_stateU_reference
    (href : referenceStateConditions D S C) :
    stateU S C.referenceState =
      fun p => D.phi p.1 * ContinuousFlexibility.Radial.cosineMode 2 p.2 :=
  funext href.1

theorem n08_stateRadialHeight_reference_hasDerivAt
    (hD : RadialProfileGeometry D) (href : referenceStateConditions D S C)
    (r : ℝ) :
    HasDerivAt (stateRadialHeight D S C C.referenceState) (D.w r) r := by
  have hw : Continuous D.w := hD.2.2.1.1.continuous
  simpa only [stateRadialHeight, n08_stateProfile_reference href] using
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable D.b r)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

/-- The zero-parameter value is proved for the actual distinguished mode
and the actual normalized primitive used in the nonlinear state. -/
theorem n08_scalarResidualField_reference_zero
    (hD : IsRadialReference D) (href : referenceStateConditions D S C)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    scalarResidualField D S C (C.referenceState, 0) p = 0 := by
  obtain ⟨bounds, hbounds⟩ := hD.1
  have hg : RadialProfileGeometry D := hbounds.1
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hphi : ContDiff ℝ ∞ D.phi := hg.2.2.2.1.1
  have hphid : ContDiff ℝ ∞ (deriv D.phi) :=
    (contDiff_infty_iff_deriv.mp hphi).2
  have hflux : ContDiff ℝ ∞ (fun r => D.w r * deriv D.phi r) := hw.mul hphid
  have hu : ContDiff ℝ ∞ (stateU S C.referenceState) := by
    rw [n08_stateU_reference href]
    exact (hphi.comp contDiff_fst).mul
      ((ContinuousFlexibility.Radial.r11b_contDiff_cosineMode 2).comp contDiff_snd)
  have hr : p.1 ≠ 0 := (hg.1.trans hp.1.1).ne'
  have hmode : ContinuousFlexibility.Radial.radialJacobi
      ((2 : ℝ) ^ 2) D.w D.phi p.1 = 0 := by
    rw [show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num]
    exact hD.2.1.1 p.1 hp.1
  calc
    _ = ContinuousFlexibility.Radial.radialPDE D.w
        (fun r θ => stateU S C.referenceState (r, θ)) p.1 p.2 := by
      change normalizedHeightResidual (stateProfile D S C C.referenceState)
        (ContinuousFlexibility.Radial.radialHeightField
          (stateRadialHeight D S C C.referenceState))
        (stateU S C.referenceState) 0 p = _
      rw [n08_stateProfile_reference href]
      exact ContinuousFlexibility.Radial.normalizedHeightResidual_radialHeightField_zero
        (n08_stateRadialHeight_reference_hasDerivAt hg href)
        (hw.differentiable (by simp) p.1) hu hr
    _ = ContinuousFlexibility.Radial.radialPDE D.w
        (fun r θ => D.phi r * ContinuousFlexibility.Radial.cosineMode 2 θ) p.1 p.2 := by
      rw [n08_stateU_reference href]
    _ = ContinuousFlexibility.Radial.radialJacobi ((2 : ℝ) ^ 2) D.w D.phi p.1 *
        ContinuousFlexibility.Radial.cosineMode 2 p.2 :=
      ContinuousFlexibility.Radial.radialPDE_cosine_lift 2
        (Eventually.of_forall fun r => hphi.differentiable (by simp) r)
        (hflux.differentiable (by simp) p.1)
    _ = 0 := by rw [hmode, zero_mul]

end ContinuousFlexibility.Statements
