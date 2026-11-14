module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Smooth zero extension across the ends of a cylinder

The Taylor series on the open cylinder extends by zero. A quadratic bound
for every jet near the boundary proves differentiability of each extended
jet there, with zero derivative. The argument also works with additional
normed-space variables carried in the second coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Asymptotics
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def zeroExtendedSeries (s : Set E) (f : E → F)
    (x : E) : FormalMultilinearSeries ℝ E F :=
  fun n => s.indicator (iteratedFDeriv ℝ n f) x

/-- A local quadratic bound for the interior jets makes their zero
extensions a genuine smooth Taylor series on the whole space. -/
theorem smooth_zero_extension_of_jet_bounds {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    (hbound : ∀ n (x : E), x ∉ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ y in 𝓝 x, y ∈ s → ‖iteratedFDeriv ℝ n f y‖ ≤ C * ‖y - x‖ ^ 2) :
    ContDiff ℝ ∞ (s.indicator f) ∧
      ∀ n (x : E), x ∉ s → iteratedFDeriv ℝ n (s.indicator f) x = 0 := by
  classical
  let J := zeroExtendedSeries s f
  have hdiff (n : ℕ) (x : E) : HasFDerivAt (fun y => J y n) (J x (n + 1)).curryLeft x := by
    by_cases hx : x ∈ s
    · have hJ : (fun y => J y n) =ᶠ[𝓝 x] iteratedFDeriv ℝ n f := by
        filter_upwards [hs.mem_nhds hx] with y hy
        simp only [J, zeroExtendedSeries, indicator_of_mem hy]
      have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
      have hd := (hf.ftaylorSeriesWithin hs.uniqueDiffOn).fderivWithin n hn x hx
      have hcurry : (ftaylorSeriesWithin ℝ f s x (n + 1)).curryLeft =
          (J x (n + 1)).curryLeft := by
        simp only [J, zeroExtendedSeries, indicator_of_mem hx, ftaylorSeriesWithin,
          iteratedFDerivWithin_of_isOpen (n + 1) hs hx]
      rw [hcurry] at hd
      apply (hd.hasFDerivAt (hs.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [hJ, hs.mem_nhds hx] with y hy hy'
      rw [hy]
      exact (iteratedFDerivWithin_of_isOpen n hs hy').symm
    · have hz (m : ℕ) : J x m = 0 := indicator_of_notMem hx _
      have hzero : HasFDerivAt (fun y => J y n) (0 : E →L[ℝ] (E [×n]→L[ℝ] F)) x := by
        obtain ⟨C, hC, hCbound⟩ := hbound n x hx
        have hO : (fun y => J y n) =O[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
          refine isBigO_iff.mpr ⟨C, ?_⟩
          filter_upwards [hCbound] with y hy
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          by_cases hys : y ∈ s
          · simpa only [J, zeroExtendedSeries, indicator_of_mem hys] using hy hys
          · simpa only [J, zeroExtendedSeries, indicator_of_notMem hys, norm_zero] using
              mul_nonneg hC (sq_nonneg ‖y - x‖)
        simpa only [hasFDerivAt_iff_isLittleO, hz n, sub_zero, zero_apply] using
          hO.trans_isLittleO (isLittleO_pow_sub_sub x (m := 2) (by decide))
      have hcurry : (0 : E [×(n + 1)]→L[ℝ] F).curryLeft = 0 := by
        ext1 v
        ext1 w
        simp only [ContinuousMultilinearMap.curryLeft_apply, zero_apply]
      rw [hz (n + 1), hcurry]
      exact hzero
  have hJ : HasFTaylorSeriesUpTo ∞ (s.indicator f) J := by
    refine ⟨?_, fun n _ x => hdiff n x, fun n _ => ?_⟩
    · intro x
      by_cases hx : x ∈ s
      · simp only [ContinuousMultilinearMap.curry0_apply, J, zeroExtendedSeries,
          indicator_of_mem hx, iteratedFDeriv_zero_apply]
      · simp only [ContinuousMultilinearMap.curry0_apply, J, zeroExtendedSeries,
          indicator_of_notMem hx, zero_apply]
    · exact continuous_iff_continuousAt.mpr fun x => (hdiff n x).continuousAt
  refine ⟨hJ.contDiff, fun n x hx => ?_⟩
  rw [← hJ.eq_iteratedFDeriv (m := n) (by simp) x]
  exact indicator_of_notMem hx _

/-- Uniform quadratic decay in the distance to the two ends is enough for
smooth zero extension, with every Fréchet jet zero on the complement. -/
theorem smooth_cylinder_zero_extension {a b : ℝ} {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (Ioo a b ×ˢ (univ : Set E)))
    (hbound : ∀ n, ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ × E, y.1 ∈ Ioo a b → min (y.1 - a) (b - y.1) < δ →
        ‖iteratedFDeriv ℝ n f y‖ ≤ (min (y.1 - a) (b - y.1)) ^ 2) :
    ContDiff ℝ ∞ ((Ioo a b ×ˢ (univ : Set E)).indicator f) ∧
      ∀ n (x : ℝ × E), x.1 ∉ Ioo a b →
        iteratedFDeriv ℝ n ((Ioo a b ×ˢ (univ : Set E)).indicator f) x = 0 := by
  let s : Set (ℝ × E) := Ioo a b ×ˢ (univ : Set E)
  have hlocal (n : ℕ) (x : ℝ × E) (hx : x ∉ s) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, y ∈ s →
        ‖iteratedFDeriv ℝ n f y‖ ≤ C * ‖y - x‖ ^ 2 := by
    obtain ⟨δ, hδ, hδbound⟩ := hbound n
    have hout : x.1 ≤ a ∨ b ≤ x.1 := by
      simpa only [s, mem_prod, mem_Ioo, mem_univ, and_true, not_and_or, not_lt] using hx
    refine ⟨1, zero_le_one, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hyball hy
    have hy' := hy.1
    have hnonneg : 0 ≤ min (y.1 - a) (b - y.1) :=
      le_min (sub_nonneg.mpr hy'.1.le) (sub_nonneg.mpr hy'.2.le)
    have hdist : min (y.1 - a) (b - y.1) ≤ ‖y - x‖ := by
      refine le_trans ?_ (norm_fst_le (y - x))
      change min (y.1 - a) (b - y.1) ≤ ‖y.1 - x.1‖
      rw [Real.norm_eq_abs]
      rcases hout with hleft | hright
      · exact (min_le_left _ _).trans ((sub_le_sub_left hleft _).trans (le_abs_self _))
      · exact (min_le_right _ _).trans (by linarith [neg_le_abs (y.1 - x.1)])
    have hnear : ‖y - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hyball
    rw [one_mul]
    exact (hδbound y hy' (hdist.trans_lt hnear)).trans
      (pow_le_pow_left₀ hnonneg hdist 2)
  have h := smooth_zero_extension_of_jet_bounds (isOpen_Ioo.prod isOpen_univ) hf hlocal
  exact ⟨h.1, fun n x hx => h.2 n x (fun hy => hx hy.1)⟩

end ContinuousFlexibility.Analysis
