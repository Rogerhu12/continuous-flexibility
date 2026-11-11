import ContinuousFlexibility.Radial.Gauge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual radial energy on a positive inner gap

The mass is taken with the physical density `12 w / r²`. A lower bound
for `r w' / w` gives the frequency coercivity used in the inner assembly.
For a homogeneous function the same energy is exactly the pairing of
its boundary values with its outward conormal derivatives. No bound on
the length of the gap, or on an off-diagonal flux entry, is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

def innerRadialGapMass (w u : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ r in a..b, (12 * w r / r ^ 2) * u r ^ 2

def innerRadialGapEnergy (w u : ℝ → ℝ) (j a b : ℝ) : ℝ :=
  ∫ r in a..b, w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2

def innerRadialGapBoundary (w u : ℝ → ℝ) (a b : ℝ) : ℝ :=
  u b * (w b * deriv u b) - u a * (w a * deriv u a)

theorem innerRadialGapMass_nonneg {a b : ℝ} (hab : a ≤ b)
    {w : ℝ → ℝ} (hw : ∀ r ∈ Icc a b, 0 ≤ w r) (u : ℝ → ℝ) :
    0 ≤ innerRadialGapMass w u a b := by
  apply intervalIntegral.integral_nonneg hab
  intro r hr
  exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hw r hr))
    (sq_nonneg _)) (sq_nonneg _)

private theorem innerGap_coefficient_bound {s r : ℝ} {w : ℝ → ℝ}
    (hr : 0 < r) (hw : 0 < w r) (hs : s ≤ r * deriv w r / w r) :
    (s / 12) * (12 * w r / r ^ 2) ≤ deriv w r / r := by
  have h := (le_div_iff₀ hw).mp hs
  calc
    _ = (s * w r) / r ^ 2 := by ring
    _ ≤ (r * deriv w r) / r ^ 2 := div_le_div_of_nonneg_right h (sq_nonneg _)
    _ = _ := by field_simp [hr.ne']; ring

/-- Frequency coercivity in the physical radial measure. In particular,
the join slope bound `2` gives the manuscript constant `1 / 6`. -/
theorem innerRadialGap_coercive {a b s : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv w r / w r) (j : ℝ) :
    (s / 12) * j ^ 2 * innerRadialGapMass w u a b ≤
      innerRadialGapEnergy w u j a b := by
  have hr : ∀ r ∈ Icc a b, 0 < r := fun r h => ha.trans_le h.1
  have hdu := (contDiff_infty_iff_deriv.mp hu).2.continuous
  have hdw := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hcM : ContinuousOn (fun r => (12 * w r / r ^ 2) * u r ^ 2) (Icc a b) :=
    ((continuous_const.mul hw.continuous).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun r h => pow_ne_zero 2 (hr r h).ne')).mul
        (hu.continuous.pow 2).continuousOn
  have hcE : ContinuousOn
      (fun r => w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2) (Icc a b) :=
    (hw.continuous.mul (hdu.pow 2)).continuousOn.add
      (((continuous_const.mul hdw).continuousOn.div continuous_id.continuousOn
        (fun r h => (hr r h).ne')).mul (hu.continuous.pow 2).continuousOn)
  unfold innerRadialGapMass innerRadialGapEnergy
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab
    ((continuousOn_const.mul hcM).intervalIntegrable_of_Icc hab)
    (hcE.intervalIntegrable_of_Icc hab)
  intro r h
  have hcoef := innerGap_coefficient_bound (hr r h) (hpos r h) (hslope r h)
  have hmul := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg j) (sq_nonneg (u r)))
  have hgrad : 0 ≤ w r * deriv u r ^ 2 := mul_nonneg (hpos r h).le (sq_nonneg _)
  nlinarith only [hmul, hgrad]

theorem innerRadialJoin_coercive {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 2 ≤ r * deriv w r / w r) (j : ℝ) :
    (1 / 6 : ℝ) * j ^ 2 * innerRadialGapMass w u a b ≤
      innerRadialGapEnergy w u j a b := by
  convert innerRadialGap_coercive hab ha hw hu hpos hslope j using 1 <;> norm_num

/-- The actual homogeneous radial equation gives the exact outgoing-flux
energy identity, including both endpoint orientations. -/
theorem innerRadialGap_energy_eq_boundary {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (heq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0) :
    innerRadialGapEnergy w u j a b = innerRadialGapBoundary w u a b := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hdw := (contDiff_infty_iff_deriv.mp hw).2
  have hflux := hw.mul hdu
  have hc : ContinuousOn
      (fun r => w r * deriv u r ^ 2 + j ^ 2 * deriv w r / r * u r ^ 2) (Icc a b) :=
    (hw.continuous.mul (hdu.continuous.pow 2)).continuousOn.add
      (((continuous_const.mul hdw.continuous).continuousOn.div continuous_id.continuousOn
        (fun r h => (ha.trans_le h.1).ne')).mul (hu.continuous.pow 2).continuousOn)
  unfold innerRadialGapEnergy innerRadialGapBoundary
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => u r * (w r * deriv u r)) _ (hc.intervalIntegrable_of_Icc hab)
  intro r hr
  have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
  have hf : deriv (fun t => w t * deriv u t) r = j ^ 2 * deriv w r / r * u r :=
    sub_eq_zero.mp (heq r hr')
  convert ((hu.differentiable (by simp) r).hasDerivAt.mul
    (hflux.differentiable (by simp) r).hasDerivAt) using 1
  rw [hf]
  ring

/-- The homogeneous mass estimate is uniform in the gap length. This is
the squared Poisson estimate before writing the boundary quadratic form
as `a* Λ a`. -/
theorem innerRadialGap_mass_le_boundary {a b j s : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv w r / w r)
    (heq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0) :
    innerRadialGapMass w u a b ≤
      innerRadialGapBoundary w u a b / ((s / 12) * j ^ 2) := by
  apply (le_div_iff₀ (mul_pos (div_pos hs (by norm_num)) (sq_pos_of_pos hj))).mpr
  have h := innerRadialGap_coercive hab ha hw hu hpos hslope j
  rw [innerRadialGap_energy_eq_boundary hab ha hw hu heq] at h
  simpa only [mul_comm (innerRadialGapMass w u a b)] using h

end ContinuousFlexibility.Radial
