module

public import ContinuousFlexibility.Analysis.OpticalTravelVariation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A fixed cutoff for quantitative optical controls

The derivative of the cutoff is the square root times the derivative of
a smooth step. Consequently its contribution involving the radial
derivative of the optical radicand is an exact derivative. The remaining
travel variation has one strict sign.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n01aOpticalStep (x : ℝ) : ℝ := Real.smoothTransition (x - 1)

theorem contDiff_n01aOpticalStep : ContDiff ℝ ∞ n01aOpticalStep :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem n01aOpticalStep_zero {x : ℝ} (hx : x ≤ 1) : n01aOpticalStep x = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)

theorem n01aOpticalStep_one {x : ℝ} (hx : 2 ≤ x) : n01aOpticalStep x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem n01aOpticalStep_nonneg (x : ℝ) : 0 ≤ n01aOpticalStep x :=
  Real.smoothTransition.nonneg _

theorem n01aOpticalStep_le_one (x : ℝ) : n01aOpticalStep x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem monotone_n01aOpticalStep : Monotone n01aOpticalStep :=
  fun _ _ h => Real.smoothTransition.monotone (sub_le_sub_right h 1)

theorem deriv_n01aOpticalStep_nonneg (x : ℝ) : 0 ≤ deriv n01aOpticalStep x :=
  monotone_n01aOpticalStep.deriv_nonneg

theorem deriv_n01aOpticalStep_zero_left {x : ℝ} (hx : x ≤ 1) :
    deriv n01aOpticalStep x = 0 := by
  have hmin : IsMinOn n01aOpticalStep univ x := isMinOn_univ_iff.mpr fun y => by
    rw [n01aOpticalStep_zero hx]
    exact n01aOpticalStep_nonneg y
  exact (hmin.isLocalMin univ_mem).deriv_eq_zero

theorem deriv_n01aOpticalStep_zero_right {x : ℝ} (hx : 2 ≤ x) :
    deriv n01aOpticalStep x = 0 := by
  have hmax : IsMaxOn n01aOpticalStep univ x := isMaxOn_univ_iff.mpr fun y => by
    rw [n01aOpticalStep_one hx]
    exact n01aOpticalStep_le_one y
  exact (hmax.isLocalMax univ_mem).deriv_eq_zero

def n01aOpticalCutoffDensity (x : ℝ) : ℝ :=
  Real.sqrt x * deriv n01aOpticalStep x

theorem n01aOpticalCutoffDensity_zero_left {x : ℝ} (hx : x ≤ 1) :
    n01aOpticalCutoffDensity x = 0 := by
  simp only [n01aOpticalCutoffDensity, deriv_n01aOpticalStep_zero_left hx, mul_zero]

theorem n01aOpticalCutoffDensity_zero_right {x : ℝ} (hx : 2 ≤ x) :
    n01aOpticalCutoffDensity x = 0 := by
  simp only [n01aOpticalCutoffDensity, deriv_n01aOpticalStep_zero_right hx, mul_zero]

theorem contDiff_n01aOpticalCutoffDensity : ContDiff ℝ ∞ n01aOpticalCutoffDensity := by
  have hd : ContDiff ℝ ∞ (deriv n01aOpticalStep) :=
    (contDiff_infty_iff_deriv.mp contDiff_n01aOpticalStep).2
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · exact (contDiffAt_id.sqrt hx.ne').mul hd.contDiffAt
  · have hx1 : x < 1 := lt_of_le_of_lt (le_of_not_gt hx) zero_lt_one
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx1] with y hy
    exact n01aOpticalCutoffDensity_zero_left hy.le

theorem n01aOpticalCutoffDensity_nonneg (x : ℝ) : 0 ≤ n01aOpticalCutoffDensity x :=
  mul_nonneg (Real.sqrt_nonneg _) (deriv_n01aOpticalStep_nonneg _)

/-- A nonnegative smooth cutoff, zero below one and constant above two. -/
def n01aOpticalCutoff (x : ℝ) : ℝ := ∫ t in (1 : ℝ)..x, n01aOpticalCutoffDensity t

theorem hasDerivAt_n01aOpticalCutoff (x : ℝ) :
    HasDerivAt n01aOpticalCutoff (n01aOpticalCutoffDensity x) x := by
  have hc := contDiff_n01aOpticalCutoffDensity.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 1 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem deriv_n01aOpticalCutoff (x : ℝ) :
    deriv n01aOpticalCutoff x = Real.sqrt x * deriv n01aOpticalStep x :=
  (hasDerivAt_n01aOpticalCutoff x).deriv

theorem contDiff_n01aOpticalCutoff : ContDiff ℝ ∞ n01aOpticalCutoff := by
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun x => (hasDerivAt_n01aOpticalCutoff x).differentiableAt, ?_⟩
  rw [show deriv n01aOpticalCutoff = n01aOpticalCutoffDensity from
    funext fun x => (hasDerivAt_n01aOpticalCutoff x).deriv]
  exact contDiff_n01aOpticalCutoffDensity

theorem n01aOpticalCutoff_zero {x : ℝ} (hx : x ≤ 1) : n01aOpticalCutoff x = 0 := by
  have he : EqOn n01aOpticalCutoffDensity (fun _ => 0) (uIcc 1 x) := by
    intro t ht
    rw [uIcc_of_ge hx] at ht
    exact n01aOpticalCutoffDensity_zero_left ht.2
  rw [n01aOpticalCutoff, intervalIntegral.integral_congr he, intervalIntegral.integral_zero]

theorem n01aOpticalCutoff_constant {x : ℝ} (hx : 2 ≤ x) :
    n01aOpticalCutoff x = n01aOpticalCutoff 2 := by
  have hc := contDiff_n01aOpticalCutoffDensity.continuous
  have hz : (∫ t in (2 : ℝ)..x, n01aOpticalCutoffDensity t) = 0 := by
    have he : EqOn n01aOpticalCutoffDensity (fun _ => 0) (uIcc 2 x) := by
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact n01aOpticalCutoffDensity_zero_right ht.1
    rw [intervalIntegral.integral_congr he, intervalIntegral.integral_zero]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 1 2) (hc.intervalIntegrable 2 x)
  simpa only [n01aOpticalCutoff, hz, add_zero] using hadd.symm

theorem n01aOpticalCutoff_nonneg (x : ℝ) : 0 ≤ n01aOpticalCutoff x := by
  by_cases hx : x ≤ 1
  · simpa only [n01aOpticalCutoff_zero hx] using (le_rfl : (0 : ℝ) ≤ 0)
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge hx)
      n01aOpticalCutoffDensity_nonneg

theorem one_le_n01aOpticalCutoff_two : 1 ≤ n01aOpticalCutoff 2 := by
  have hstep := contDiff_n01aOpticalStep.differentiable (by simp)
  have hd := (contDiff_infty_iff_deriv.mp contDiff_n01aOpticalStep).2.continuous
  have hi : (∫ t in (1 : ℝ)..2, deriv n01aOpticalStep t) = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hstep t).hasDerivAt) (hd.intervalIntegrable 1 2),
      n01aOpticalStep_one le_rfl, n01aOpticalStep_zero le_rfl]
    norm_num
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    (hd.intervalIntegrable 1 2) (contDiff_n01aOpticalCutoffDensity.continuous.intervalIntegrable 1 2)
    (fun t ht => show deriv n01aOpticalStep t ≤ n01aOpticalCutoffDensity t from by
      have hsqrt : 1 ≤ Real.sqrt t := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht.1
      exact le_mul_of_one_le_left (deriv_n01aOpticalStep_nonneg t) hsqrt)
  simpa only [hi, n01aOpticalCutoff] using hmono

theorem one_le_n01aOpticalCutoff {x : ℝ} (hx : 2 ≤ x) : 1 ≤ n01aOpticalCutoff x := by
  rw [n01aOpticalCutoff_constant hx]
  exact one_le_n01aOpticalCutoff_two

/-- Every derivative of this one fixed cutoff has a global finite bound. -/
theorem n01aOpticalCutoff_jet_bound (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, |iteratedDeriv s n01aOpticalCutoff x| ≤ B := by
  have hc := contDiff_n01aOpticalCutoff.continuous_iteratedDeriv s (by simp)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1 : ℝ) 2) hc.continuousOn
  let B := 1 + |K| + |n01aOpticalCutoff 2|
  have hB : 0 < B := by dsimp [B]; positivity
  have hKB : K ≤ B := by dsimp [B]; linarith [le_abs_self K, abs_nonneg (n01aOpticalCutoff 2)]
  have hplateau : |n01aOpticalCutoff 2| ≤ B := by dsimp [B]; linarith [abs_nonneg K]
  refine ⟨B, hB, fun x => ?_⟩
  by_cases hx : x < 1
  · have he : n01aOpticalCutoff =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact n01aOpticalCutoff_zero hy.le
    rw [he.iteratedDeriv_eq s, iteratedDeriv_fun_const_zero, abs_zero]
    exact hB.le
  · by_cases hx' : 2 < x
    · have he : n01aOpticalCutoff =ᶠ[𝓝 x] (fun _ : ℝ => n01aOpticalCutoff 2) := by
        filter_upwards [Ioi_mem_nhds hx'] with y hy
        exact n01aOpticalCutoff_constant hy.le
      rw [he.iteratedDeriv_eq s, iteratedDeriv_const]
      split_ifs
      · exact hplateau
      · simpa only [abs_zero] using hB.le
    · have hk : |iteratedDeriv s n01aOpticalCutoff x| ≤ K := by
        simpa only [Real.norm_eq_abs] using hK x ⟨le_of_not_gt hx, le_of_not_gt hx'⟩
      exact hk.trans hKB

end ContinuousFlexibility.Statements
