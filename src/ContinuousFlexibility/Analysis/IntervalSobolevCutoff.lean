import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

/-!
# Smooth cutoff of an interval function onto the half-line

The input is smooth only on the closed interval. A cutoff that vanishes
before its far endpoint makes its product smooth on the whole half-line.
The derivative formula uses the actual derivatives within the interval,
including both endpoints. The same result applies to either endpoint after
an affine change of coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

private def intervalCutoffBump (L : ℝ) (hL : 0 < L) : ContDiffBump (0 : ℝ) where
  rIn := L / 3
  rOut := 2 * L / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- A fixed smooth cutoff with a left plateau. It is one on `(-∞, L/3]`
and zero on `[2L/3, ∞)`. -/
def intervalSobolevCutoff (L : ℝ) (hL : 0 < L) (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 else intervalCutoffBump L hL x

theorem intervalSobolevCutoff_one (L : ℝ) (hL : 0 < L) {x : ℝ}
    (hx : x ≤ L / 3) : intervalSobolevCutoff L hL x = 1 := by
  by_cases hx0 : x ≤ 0
  · exact if_pos hx0
  · rw [intervalSobolevCutoff, if_neg hx0]
    apply (intervalCutoffBump L hL).one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero,
      abs_of_nonneg (le_of_not_ge hx0)]
    exact hx

theorem intervalSobolevCutoff_zero (L : ℝ) (hL : 0 < L) {x : ℝ}
    (hx : 2 * L / 3 ≤ x) : intervalSobolevCutoff L hL x = 0 := by
  have hx0 : 0 < x := by linarith
  rw [intervalSobolevCutoff, if_neg (not_le.mpr hx0)]
  apply (intervalCutoffBump L hL).zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0.le]
  exact hx

theorem intervalSobolevCutoff_range (L : ℝ) (hL : 0 < L) (x : ℝ) :
    intervalSobolevCutoff L hL x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : x ≤ 0
  · simp only [intervalSobolevCutoff, if_pos hx, mem_Icc]
    exact ⟨zero_le_one, le_rfl⟩
  · rw [intervalSobolevCutoff, if_neg hx]
    exact ⟨(intervalCutoffBump L hL).nonneg, (intervalCutoffBump L hL).le_one⟩

theorem contDiff_intervalSobolevCutoff (L : ℝ) (hL : 0 < L) :
    ContDiff ℝ ∞ (intervalSobolevCutoff L hL) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x < L / 3
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (1 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact intervalSobolevCutoff_one L hL hy.le
  · have hx0 : 0 < x := by linarith
    apply (intervalCutoffBump L hL).contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    exact if_neg (not_le.mpr hy)

theorem intervalSobolevCutoff_eventually_one (L : ℝ) (hL : 0 < L) :
    intervalSobolevCutoff L hL =ᶠ[𝓝 0] (fun _ => 1) := by
  filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) < L / 3 by linarith)] with x hx
  exact intervalSobolevCutoff_one L hL hx.le

/-- Every derivative of the fixed cutoff is bounded; the bound may depend
on the derivative order and on the interval length. -/
theorem intervalSobolevCutoff_deriv_bounded (L : ℝ) (hL : 0 < L) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedDeriv n (intervalSobolevCutoff L hL) x‖ ≤ C := by
  have hc : Continuous (iteratedDeriv n (intervalSobolevCutoff L hL)) :=
    (contDiff_intervalSobolevCutoff L hL).continuous_iteratedDeriv n (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) L) hc.continuousOn
  refine ⟨max 1 C, zero_le_one.trans (le_max_left _ _), fun x => ?_⟩
  by_cases hx0 : x < 0
  · have he : intervalSobolevCutoff L hL =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds (show x < L / 3 by linarith)] with y hy
      exact intervalSobolevCutoff_one L hL hy.le
    rw [Filter.EventuallyEq.iteratedDeriv_eq n he, iteratedDeriv_const]
    split_ifs
    · simpa only [norm_one] using le_max_left (1 : ℝ) C
    · simpa only [norm_zero] using zero_le_one.trans (le_max_left (1 : ℝ) C)
  · by_cases hxL : L < x
    · have he : intervalSobolevCutoff L hL =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show 2 * L / 3 < x by linarith)] with y hy
        exact intervalSobolevCutoff_zero L hL hy.le
      rw [Filter.EventuallyEq.iteratedDeriv_eq n he, iteratedDeriv_fun_const_zero, norm_zero]
      exact zero_le_one.trans (le_max_left _ _)
    · exact (hC x ⟨le_of_not_gt hx0, le_of_not_gt hxL⟩).trans (le_max_right _ _)

section HalfLine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Scalar cutoff on actual functions. Vanishing of `χ` beyond the interval
makes this a half-line function without reading exterior input values. -/
def cutoffHalfLine (χ : ℝ → ℝ) (f : ℝ → F) (x : ℝ) : F := χ x • f x

theorem cutoffHalfLine_eq_smul (χ : ℝ → ℝ) (f : ℝ → F) : cutoffHalfLine χ f = χ • f := by
  funext x
  exact (Pi.smul_apply χ f x).symm

theorem cutoffHalfLine_add (χ : ℝ → ℝ) (f g : ℝ → F) :
    cutoffHalfLine χ (f + g) = cutoffHalfLine χ f + cutoffHalfLine χ g := by
  funext x
  simp only [cutoffHalfLine, Pi.add_apply, smul_add]

theorem cutoffHalfLine_smul (χ : ℝ → ℝ) (a : ℝ) (f : ℝ → F) :
    cutoffHalfLine χ (a • f) = a • cutoffHalfLine χ f := by
  funext x
  simp only [cutoffHalfLine, Pi.smul_apply, smul_smul, mul_comm]

theorem cutoffHalfLine_zero_of_vanishing {χ : ℝ → ℝ} (f : ℝ → F) {c x : ℝ}
    (hχ : ∀ y, c ≤ y → χ y = 0) (hx : c ≤ x) : cutoffHalfLine χ f x = 0 := by
  rw [cutoffHalfLine, hχ x hx, zero_smul]

theorem cutoffHalfLine_eventually_zero {χ : ℝ → ℝ} (f : ℝ → F) {c x : ℝ}
    (hχ : ∀ y, c ≤ y → χ y = 0) (hx : c < x) :
    cutoffHalfLine χ f =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact cutoffHalfLine_zero_of_vanishing f hχ hy.le

/-- The smoothness assumption concerns only the original closed interval. -/
theorem contDiffOn_cutoffHalfLine_of_vanishing {L c : ℝ} (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Icc 0 L)) :
    ContDiffOn ℝ ∞ (cutoffHalfLine χ f) (Ici 0) := by
  intro x hx
  by_cases hxL : x < L
  · have hmem : Icc (0 : ℝ) L ∈ 𝓝[Ici 0] x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds hxL)] with y hy0 hyL
      exact ⟨hy0, hyL.le⟩
    exact hχ.contDiffAt.contDiffWithinAt.smul
      ((hf x ⟨hx, hxL.le⟩).mono_of_mem_nhdsWithin hmem)
  · have hcx : c < x := hc.trans_le (le_of_not_gt hxL)
    exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : F)) x).congr_of_eventuallyEq
      (cutoffHalfLine_eventually_zero f hzero hcx)).contDiffWithinAt

theorem iteratedDerivWithin_cutoffHalfLine_zero {χ : ℝ → ℝ} (f : ℝ → F)
    {c x : ℝ} (hχ : ∀ y, c ≤ y → χ y = 0) (hx : c < x)
    (n : ℕ) (s : Set ℝ) : iteratedDerivWithin n (cutoffHalfLine χ f) s x = 0 := by
  have he := cutoffHalfLine_eventually_zero f hχ hx
  have hd := Filter.EventuallyEq.iteratedDerivWithin_eq (n := n) (s := s)
    (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds
  simpa only [iteratedDerivWithin_fun_const_zero] using hd

/-- Restricting a smooth half-line jet to a nondegenerate closed interval
does not change it, even at the endpoints. -/
theorem iteratedDerivWithin_Icc_eq_Ici {L : ℝ} (hL : 0 < L) {f : ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    iteratedDerivWithin n f (Icc 0 L) x = iteratedDerivWithin n f (Ici 0) x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_subset Icc_subset_Ici_self (uniqueDiffOn_Icc hL)
      (uniqueDiffOn_Ici 0) (hf.of_le (by simp)) hx]

/-- Leibniz's rule for the actual half-line derivatives in terms of the
original interval derivatives, at every point of the closed interval. -/
theorem iteratedDerivWithin_cutoffHalfLine {L c : ℝ} (hL : 0 < L) (hc : c < L)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ y, c ≤ y → χ y = 0)
    {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Icc 0 L))
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    iteratedDerivWithin n (cutoffHalfLine χ f) (Ici 0) x =
      ∑ i ∈ Finset.range (n + 1), n.choose i •
        iteratedDeriv i χ x • iteratedDerivWithin (n - i) f (Icc 0 L) x := by
  have hg := contDiffOn_cutoffHalfLine_of_vanishing hc hχ hzero hf
  rw [← iteratedDerivWithin_Icc_eq_Ici hL hg n hx, cutoffHalfLine_eq_smul,
    iteratedDerivWithin_smul hx (uniqueDiffOn_Icc hL)
      (hχ.contDiffAt.contDiffWithinAt.of_le (by simp)) ((hf x hx).of_le (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hL)
    (hχ.contDiffAt.of_le (by simp)) hx]

end HalfLine

end ContinuousFlexibility.Analysis
