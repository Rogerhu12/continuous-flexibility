import ContinuousFlexibility.Radial.SeedConnectorInterpolation
import ContinuousFlexibility.Radial.SeedConnectorReconstruction

/-!
# Cutting the actual central logarithmic slope to the two cone slopes

The cut positions are chosen from the proved C¹ asymptotics.  The prescribed
slope agrees with the actual central solution on an interval containing both
turning points, is exactly ±2 on the outer half-lines, and has positive
profile derivative on the two added connecting intervals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem connectorRetainWeight_one_germ (right : Bool) (cut y : ℝ)
    (hy : if right then y < cut + 1 / 2 else cut - 1 / 2 < y) :
    connectorRetainWeight right cut =ᶠ[𝓝 y] fun _ => 1 := by
  cases right with
  | false =>
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact connectorRetainWeight_one false cut t ht.le
  | true =>
    filter_upwards [Iio_mem_nhds hy] with t ht
    exact connectorRetainWeight_one true cut t ht.le

/-- Quantitative data for a slope after both cone cutoffs. -/
structure SeedSlopeCutoff (original : ℝ → ℝ) (aL aR lower upper : ℝ) where
  left : ℝ
  right : ℝ
  slope : ℝ → ℝ
  left_neg : left < 0
  right_pos : 0 < right
  left_turn : left < lower
  right_turn : upper < right
  smooth : ContDiff ℝ ∞ slope
  below_four : ∀ y, slope y < 4
  retained : ∀ y ∈ Icc left right, slope y = original y
  left_cone : ∀ y, y ≤ left - 1 → slope y = aL
  right_cone : ∀ y, right + 1 ≤ y → slope y = aR
  positive_left : ∀ y, y ≤ left →
    (3 / 4 : ℝ) ≤ (slope y ^ 2 - slope y + deriv slope y) / (4 - slope y)
  positive_right : ∀ y, right ≤ y →
    (3 / 4 : ℝ) ≤ (slope y ^ 2 - slope y + deriv slope y) / (4 - slope y)

theorem exists_seedSlopeCutoff {k₀ : ℝ → ℝ} {aL aR : ℝ}
    (hk₀ : ContDiff ℝ ∞ k₀) (hk₀4 : ∀ y, k₀ y < 4)
    (haL : aL ^ 2 = 4) (haR : aR ^ 2 = 4)
    (hlimL : Tendsto k₀ atBot (𝓝 aL) ∧ Tendsto (deriv k₀) atBot (𝓝 0))
    (hlimR : Tendsto k₀ atTop (𝓝 aR) ∧ Tendsto (deriv k₀) atTop (𝓝 0))
    (lower upper : ℝ) : Nonempty (SeedSlopeCutoff k₀ aL aR lower upper) := by
  have haL4 : aL < 4 := by nlinarith [sq_nonneg (aL - 2)]
  have haR4 : aR < 4 := by nlinarith [sq_nonneg (aR - 2)]
  obtain ⟨B, hB, hBd⟩ := exists_connectorRetainWeight_derivative_bound
  let ε := connectorInterpolationTolerance B
  have hε : 0 < ε := connectorInterpolationTolerance_pos hB.le
  have hleft : ∀ᶠ y in atBot, |k₀ y - aL| ≤ ε ∧ |deriv k₀ y| ≤ ε := by
    filter_upwards [(Metric.tendsto_nhds.mp hlimL.1) ε hε,
      (Metric.tendsto_nhds.mp hlimL.2) ε hε] with y hy hy'
    exact ⟨by simpa only [Real.dist_eq] using hy.le,
      by simpa only [Real.dist_eq, sub_zero] using hy'.le⟩
  have hright : ∀ᶠ y in atTop, |k₀ y - aR| ≤ ε ∧ |deriv k₀ y| ≤ ε := by
    filter_upwards [(Metric.tendsto_nhds.mp hlimR.1) ε hε,
      (Metric.tendsto_nhds.mp hlimR.2) ε hε] with y hy hy'
    exact ⟨by simpa only [Real.dist_eq] using hy.le,
      by simpa only [Real.dist_eq, sub_zero] using hy'.le⟩
  obtain ⟨u, hu⟩ := eventually_atBot.mp hleft
  obtain ⟨v, hv⟩ := eventually_atTop.mp hright
  let L := min u (min 0 lower) - 2
  let H := max v (max 0 upper) + 2
  have hLu : L ≤ u := by
    dsimp only [L]
    linarith [min_le_left u (min 0 lower)]
  have hLn : L < 0 := by
    dsimp only [L]
    linarith [min_le_right u (min 0 lower),
      min_le_left (0 : ℝ) lower]
  have hLt : L < lower := by
    dsimp only [L]
    linarith [min_le_right u (min 0 lower),
      min_le_right (0 : ℝ) lower]
  have hvH : v ≤ H := by
    dsimp only [H]
    linarith [le_max_left v (max 0 upper)]
  have hHp : 0 < H := by
    dsimp only [H]
    linarith [le_max_right v (max 0 upper),
      le_max_left (0 : ℝ) upper]
  have hHt : upper < H := by
    dsimp only [H]
    linarith [le_max_right v (max 0 upper),
      le_max_right (0 : ℝ) upper]
  let kL := connectorInterpolatedSlope (connectorRetainWeight false L) k₀ aL
  let k := connectorInterpolatedSlope (connectorRetainWeight true H) kL aR
  have hkL : ContDiff ℝ ∞ kL :=
    connectorInterpolatedSlope_contDiff (connectorRetainWeight_contDiff false L) hk₀ aL
  have hk : ContDiff ℝ ∞ k :=
    connectorInterpolatedSlope_contDiff (connectorRetainWeight_contDiff true H) hkL aR
  have hkL4 (y : ℝ) : kL y < 4 := by
    apply connectorInterpolatedSlope_lt_four
      (connectorRetainWeight_bounds false L y).1
      (connectorRetainWeight_bounds false L y).2 haL4
    exact hk₀4 y
  have hk4 (y : ℝ) : k y < 4 :=
    connectorInterpolatedSlope_lt_four
      (connectorRetainWeight_bounds true H y).1
      (connectorRetainWeight_bounds true H y).2 haR4 (hkL4 y)
  have hkL_germ (y : ℝ) (hy : L - 1 / 2 < y) : kL =ᶠ[𝓝 y] k₀ :=
    connectorInterpolatedSlope_germ_of_one
      (connectorRetainWeight_one_germ false L y hy)
  have hk_germ (y : ℝ) (hy : y < H + 1 / 2) : k =ᶠ[𝓝 y] kL :=
    connectorInterpolatedSlope_germ_of_one
      (connectorRetainWeight_one_germ true H y hy)
  refine ⟨⟨L, H, k, hLn, hHp, hLt, hHt, hk, hk4, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y hy
    exact (hk_germ y (by linarith [hy.2])).eq_of_nhds.trans
      (hkL_germ y (by linarith [hy.1])).eq_of_nhds
  · intro y hy
    rw [(hk_germ y (by linarith)).eq_of_nhds]
    exact connectorInterpolatedSlope_eq_of_zero
      (connectorRetainWeight_zero false L y hy)
  · intro y hy
    exact connectorInterpolatedSlope_eq_of_zero
      (connectorRetainWeight_zero true H y hy)
  · intro y hy
    have hg := hk_germ y (by linarith)
    rw [hg.eq_of_nhds, hg.deriv_eq]
    exact (connectorInterpolatedSlope_admissible
      ((connectorRetainWeight_contDiff false L).differentiable (by simp) y)
      (hk₀.differentiable (by simp) y) haL hB.le
      (connectorRetainWeight_bounds false L y).1
      (connectorRetainWeight_bounds false L y).2 (hBd false L y)
      (hu y (hy.trans hLu)).1 (hu y (hy.trans hLu)).2).2
  · intro y hy
    have hg := hkL_germ y (by linarith)
    have hb := hv y (hvH.trans hy)
    apply (connectorInterpolatedSlope_admissible
      ((connectorRetainWeight_contDiff true H).differentiable (by simp) y)
      (hkL.differentiable (by simp) y) haR hB.le
      (connectorRetainWeight_bounds true H y).1
      (connectorRetainWeight_bounds true H y).2 (hBd true H y) ?_ ?_).2
    · rw [hg.eq_of_nhds]
      exact hb.1
    · rw [hg.deriv_eq]
      exact hb.2

abbrev SeedCentralCutoff :=
  SeedSlopeCutoff (seedLogSlope centralKernelHeight) 2 (-2)
    (log (centralRadius (-sqrt centralOscillatorA)))
    (log (centralRadius (sqrt centralOscillatorA)))

theorem exists_seedCentralCutoff : Nonempty SeedCentralCutoff :=
  exists_seedSlopeCutoff contDiff_centralSeedLogSlope
    (fun y => (centralSeedLogSlope_lt_two y).trans (by norm_num))
    (by norm_num) (by norm_num)
    centralSeedLogSlope_log_C1_left centralSeedLogSlope_log_C1_right _ _

end ContinuousFlexibility.Radial
