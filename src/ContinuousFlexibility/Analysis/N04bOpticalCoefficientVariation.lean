import ContinuousFlexibility.Analysis.N04bOpticalHeightVariation

/-!
# Variation of the actual corrected characteristic coefficients

The drift and speed formulas here are transferred to `b/a` and
`sqrt (b² - a*c)/a` for the corrected scalar operator. Positivity persists
along the genuine height family near zero, so this transfer is an equality
of functions on a parameter neighborhood, rather than only at the base.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Height compatibility simplifies the characteristic drift to the
normalized mixed coefficient. -/
theorem n04b_characteristicDrift_eq_mixed_ratio
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiffAt ℝ 2 z x) (hr : x.1 ≠ 0) :
    characteristicDrift w z x =
      -profileEnergy w x * radialPartial (heightAngular z) x /
        heightQ (profileEnergy w x) (heightRadial z x)
          (angularPartial (heightAngular z) x) := by
  have hc := height_compatibility hz hr
  have hn : heightAngular z x - angularPartial (heightRadial z) x =
      -(x.1 * radialPartial (heightAngular z) x) := by linarith only [hc]
  unfold characteristicDrift
  rw [hn, show profileEnergy w x * -(x.1 * radialPartial (heightAngular z) x) =
    x.1 * (-profileEnergy w x * radialPartial (heightAngular z) x) by ring,
    mul_div_mul_left _ _ hr]

/-- The drift is exactly the ratio of the actual mixed and radial
principal coefficients. -/
theorem n04b_characteristicDrift_eq_corrected_ratio
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : ContDiffAt ℝ 2 z x) (hr : x.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z x)
    (hQ : 0 < heightQ (profileEnergy w x) (heightRadial z x)
      (angularPartial (heightAngular z) x)) :
    characteristicDrift w z x = polarLinearB w z x / polarLinearA w z x := by
  have ha : 0 < polarLinearA w z x := mul_pos hQ (inverseDThreeHalves_pos _ hD)
  apply (eq_div_iff ha.ne').mpr
  rw [mul_comm]
  exact polarLinearA_mul_characteristicDrift hz hr hQ.ne'

/-- Actual height perturbations have the expected mixed-derivative drift
variation at a radial reference height. -/
theorem n04b_hasDerivAt_characteristicDrift_radialHeight
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hr : 0 < x.1) (hwp : 0 < w x.1) :
    HasDerivAt
      (fun q => characteristicDrift w (heightFamily (radialHeightField h) u q) x)
      (-(1 + w x.1 ^ 2) / (x.1 * w x.1) *
        (angularPartial (radialPartial u) x - angularPartial u x / x.1)) 0 := by
  have hH := contDiff_radialHeightField hh
  have hQ := n04b_hasDerivAt_heightQ_heightFamily w hH hu hr.ne'
  have hQ0 : heightQ (profileEnergy w x)
      (heightRadial (heightFamily (radialHeightField h) u 0) x)
      (angularPartial (heightAngular (heightFamily (radialHeightField h) u 0)) x) =
      w x.1 := by rw [heightFamily_zero, n04b_heightQ_radialHeightField hhw]
  have hd := ((hasDerivAt_radialPartial_heightAngular_heightFamily hH hu hr.ne' 0).const_mul
    (-profileEnergy w x)).div hQ (by rw [hQ0]; exact hwp.ne')
  have heq : (fun q => characteristicDrift w (heightFamily (radialHeightField h) u q) x) =
      fun q => -profileEnergy w x *
        radialPartial (heightAngular (heightFamily (radialHeightField h) u q)) x /
        heightQ (profileEnergy w x)
          (heightRadial (heightFamily (radialHeightField h) u q) x)
          (angularPartial (heightAngular (heightFamily (radialHeightField h) u q)) x) := by
    funext q
    exact n04b_characteristicDrift_eq_mixed_ratio
      ((contDiff_heightFamily hH hu q).contDiffAt.of_le (by simp)) hr.ne'
  rw [heq]
  apply hd.congr_deriv
  simp only [hQ0, heightFamily_zero, heightAngular_radialHeightField hhw,
    radialPartial_const, mul_zero, zero_mul, sub_zero]
  have hc := height_compatibility (hu.contDiffAt.of_le (by simp)) hr.ne'
  have hp : radialPartial (heightAngular u) x =
      (angularPartial (heightRadial u) x - heightAngular u x) / x.1 := by
    apply (eq_div_iff hr.ne').mpr
    rw [mul_comm]
    exact hc
  rw [hp]
  unfold profileEnergy radialEnergy heightRadial heightAngular
  field_simp [hr.ne', hwp.ne']
  <;> ring

/-- The actual radial height family remains in the positive discriminant
and positive denominator branch for all sufficiently small parameters. -/
theorem n04b_eventually_admissible_radialHeightFamily
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hr : x.1 ≠ 0) (hwp : 0 < w x.1) :
    ∀ᶠ q in 𝓝 (0 : ℝ),
      0 < polarDiscriminant w (heightFamily (radialHeightField h) u q) x ∧
      0 < heightQ (profileEnergy w x)
        (heightRadial (heightFamily (radialHeightField h) u q) x)
        (angularPartial (heightAngular (heightFamily (radialHeightField h) u q)) x) := by
  have hH := contDiff_radialHeightField hh
  have hD := hasDerivAt_polarDiscriminant_heightFamily w hH hu x
  have hQ := n04b_hasDerivAt_heightQ_heightFamily w hH hu hr
  have hDpos : 0 < polarDiscriminant w (heightFamily (radialHeightField h) u 0) x := by
    rw [heightFamily_zero, polarDiscriminant_radialHeightField hhw]
    exact zero_lt_one
  have hQpos : 0 < heightQ (profileEnergy w x)
      (heightRadial (heightFamily (radialHeightField h) u 0) x)
      (angularPartial (heightAngular (heightFamily (radialHeightField h) u 0)) x) := by
    rw [heightFamily_zero, n04b_heightQ_radialHeightField hhw]
    exact hwp
  exact (continuousAt_const.eventually_lt hD.continuousAt hDpos).and
    (continuousAt_const.eventually_lt hQ.continuousAt hQpos)

/-- The drift variation is a derivative of the actual quotient `b/a`. -/
theorem n04b_hasDerivAt_correctedDrift_radialHeight
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hu : ContDiff ℝ ∞ u) (hr : 0 < x.1) (hwp : 0 < w x.1) :
    HasDerivAt (fun q =>
      polarLinearB w (heightFamily (radialHeightField h) u q) x /
        polarLinearA w (heightFamily (radialHeightField h) u q) x)
      (-(1 + w x.1 ^ 2) / (x.1 * w x.1) *
        (angularPartial (radialPartial u) x - angularPartial u x / x.1)) 0 := by
  apply (n04b_hasDerivAt_characteristicDrift_radialHeight hh hhw hu hr hwp).congr_of_eventuallyEq
  filter_upwards [n04b_eventually_admissible_radialHeightFamily hh hhw hu hr.ne' hwp]
    with q hq
  exact (n04b_characteristicDrift_eq_corrected_ratio
    ((contDiff_heightFamily (contDiff_radialHeightField hh) hu q).contDiffAt.of_le (by simp))
    hr.ne' hq.1 hq.2).symm

/-- The speed variation is a derivative of the actual corrected
determinant quotient, with the positive square-root branch proved locally. -/
theorem n04b_hasDerivAt_correctedSpeed_radialHeight
    {h w : ℝ → ℝ} {u : PolarPoint → ℝ} {x : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hhw : ∀ r, HasDerivAt h (w r) r)
    (hw : DifferentiableAt ℝ w x.1) (hu : ContDiff ℝ ∞ u)
    (hr : 0 < x.1) (hwp : 0 < w x.1) (hwn : deriv w x.1 < 0) :
    HasDerivAt (fun q =>
      Real.sqrt (polarLinearB w (heightFamily (radialHeightField h) u q) x ^ 2 -
        polarLinearA w (heightFamily (radialHeightField h) u q) x *
          polarCorrectedC w (heightFamily (radialHeightField h) u q) x) /
        polarLinearA w (heightFamily (radialHeightField h) u q) x)
      (-opticalSpeed w x.1 * (1 + w x.1 ^ 2) / w x.1 *
        (radialPartial u x + angularPartial (angularPartial u) x / x.1)) 0 := by
  apply (n04b_hasDerivAt_characteristicSpeed_radialHeight hh hhw hu hr hwp).congr_of_eventuallyEq
  filter_upwards [n04b_eventually_admissible_radialHeightFamily hh hhw hu hr.ne' hwp]
    with q hq
  exact (n04b_characteristicSpeed_eq_corrected_ratio hw hr hwp hwn hq.1 hq.2).symm

end ContinuousFlexibility.Statements
