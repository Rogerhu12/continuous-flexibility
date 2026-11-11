import ContinuousFlexibility.Analysis.OneHighCircleFlowTimeChange
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Joint smoothness on the original open time strip

A smooth time change can be chosen affine near any interior time, while
remaining inside the supplied closed interval and starting at its initial
time. The smooth reparametrized flow then agrees locally with the original
flow after an explicit affine change of coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem exists_circleFlow_localTime {a b t : ℝ} (ht : t ∈ Ioo a b) :
    ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = a ∧
      (∀ s : ℝ, τ s ∈ Icc a b) ∧
      ∀ s : ℝ, |s - 2| ≤ 1 / 4 →
        τ s = t + min (t - a) (b - t) * (s - 2) := by
  let ε : ℝ := min (t - a) (b - t)
  have hε : 0 < ε := lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
  have hεa : ε ≤ t - a := min_le_left _ _
  have hεb : ε ≤ b - t := min_le_right _ _
  let χ : ContDiffBump (2 : ℝ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let τ : ℝ → ℝ := fun s => (1 - χ s) * circleFlowCompactTime a b s +
    χ s * (t + ε * (s - 2))
  have hχ : ContDiff ℝ ∞ (fun s : ℝ => χ s) := χ.contDiff
  have hτ : ContDiff ℝ ∞ τ :=
    ((contDiff_const.sub hχ).mul (contDiff_circleFlowCompactTime a b)).add
      (hχ.mul (contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const))))
  have hχzero : χ 0 = 0 := χ.zero_of_le_dist (by norm_num [χ, Real.dist_eq])
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · simp only [τ, hχzero, sub_zero, one_mul, zero_mul, add_zero,
      circleFlowCompactTime_zero]
  · intro s
    have hbase := circleFlowCompactTime_mem (ht.1.le.trans ht.2.le) s
    by_cases hz : χ s = 0
    · simpa only [τ, hz, sub_zero, one_mul, zero_mul, add_zero] using hbase
    · have hs : s ∈ Metric.ball (2 : ℝ) χ.rOut := by
        rw [← χ.support_eq]
        exact hz
      have hs' : -1 ≤ s - 2 ∧ s - 2 ≤ 1 := by
        have hh : |s - 2| < (1 / 2 : ℝ) := by
          simpa only [χ, Metric.mem_ball, Real.dist_eq] using hs
        have hh' := abs_lt.mp hh
        constructor <;> linarith
      have hlo := mul_le_mul_of_nonneg_left hs'.1 hε.le
      have hhi := mul_le_mul_of_nonneg_left hs'.2 hε.le
      have hlinear : t + ε * (s - 2) ∈ Icc a b := by
        constructor <;> linarith
      have hleft : 0 ≤ 1 - χ s := sub_nonneg.mpr χ.le_one
      have hsum : (1 - χ s) + χ s = 1 := by ring
      simpa only [τ, smul_eq_mul] using
        (convex_Icc a b) hbase hlinear hleft χ.nonneg hsum
  · intro s hs
    have hs' : s ∈ Metric.closedBall (2 : ℝ) χ.rIn := by
      simpa only [χ, Metric.mem_closedBall, Real.dist_eq] using hs
    have hone := χ.one_of_mem_closedBall hs'
    simp only [τ, hone, sub_self, zero_mul, one_mul, zero_add]

/-- The supplied classical flow is jointly smooth at every interior time.
The proof uses a local affine part of a smooth time change, not an
extension of the flow outside its stated time interval. -/
theorem circleFlow_contDiffAt {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {p : PolarPoint} (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ ∞ Θ p := by
  let ε : ℝ := min (p.1 - a) (b - p.1)
  have hε : 0 < ε := lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2)
  obtain ⟨τ, hτ, hτzero, hτrange, hτlinear⟩ := exists_circleFlow_localTime hp
  have hsmooth := contDiff_circleFlow_timeChange hG hP hperiod hΘ hinit hflow
    hτ hτzero hτrange
  let I : ℝ → ℝ := fun r => 2 + (r - p.1) / ε
  have hI : ContDiff ℝ ∞ I :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).div_const ε)
  have hcomp : ContDiff ℝ ∞ (fun q : PolarPoint => Θ (τ (I q.1), q.2)) :=
    hsmooth.comp ((hI.comp contDiff_fst).prodMk contDiff_snd)
  apply hcomp.contDiffAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p,
      q.1 ∈ Ioo (p.1 - ε / 4) (p.1 + ε / 4) :=
    continuous_fst.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hnear] with q hq
  have harg : |I q.1 - 2| ≤ (1 / 4 : ℝ) := by
    have he : I q.1 - 2 = (q.1 - p.1) / ε := by dsimp only [I]; ring
    rw [he, abs_div, abs_of_pos hε]
    apply (div_le_iff₀ hε).mpr
    apply abs_le.mpr
    constructor <;> linarith [hq.1, hq.2]
  have htime : τ (I q.1) = q.1 := by
    rw [hτlinear (I q.1) harg]
    have he : min (p.1 - a) (b - p.1) = ε := by rfl
    rw [he]
    dsimp only [I]
    field_simp [hε.ne'] <;> ring
  exact congrArg (fun r => Θ (r, q.2)) htime.symm

theorem circleFlow_contDiffOn_open {G Θ : PolarPoint → ℝ} {a b P : ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : 0 < P)
    (hperiod : ∀ t : ℝ, Function.Periodic (fun θ => G (t, θ)) P)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) :
    ContDiffOn ℝ ∞ Θ (Ioo a b ×ˢ (univ : Set ℝ)) := by
  intro p hp
  exact (circleFlow_contDiffAt hG hP hperiod hΘ hinit hflow hp.1).contDiffWithinAt

end ContinuousFlexibility.Analysis
