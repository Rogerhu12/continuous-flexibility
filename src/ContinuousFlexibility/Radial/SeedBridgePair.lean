import ContinuousFlexibility.Radial.SeedPositiveBridge
import ContinuousFlexibility.Radial.SeedConnectorReconstruction
import ContinuousFlexibility.Radial.SeedLogSlopeLower

/-! # A positive bridge between the two pure cone modes -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff

structure SeedBridgePair where
  profile : ℝ → ℝ
  height : ℝ → ℝ
  left : ℝ
  right : ℝ
  left_pos : 0 < left
  ordered : left < right
  profile_smooth : ContDiffOn ℝ ∞ profile (Ioi 0)
  height_smooth : ContDiffOn ℝ ∞ height (Ioi 0)
  positive : ∀ r, 0 < r → 0 < profile r
  increasing : ∀ r, 0 < r → 0 < deriv profile r
  homogeneous : ∀ r, 0 < r → radialJacobi 4 profile height r = 0
  leftScale : ℝ
  rightScale : ℝ
  leftHeight : ℝ
  rightHeight : ℝ
  leftScale_pos : 0 < leftScale
  rightScale_pos : 0 < rightScale
  leftHeight_pos : 0 < leftHeight
  rightHeight_pos : 0 < rightHeight
  left_eq : ∀ r, 0 < r → r < left →
    profile r = leftScale * r ∧ height r = leftHeight * r ^ (-2 : ℝ)
  right_eq : ∀ r, right < r →
    profile r = rightScale * r ∧ height r = rightHeight * r ^ (2 : ℝ)

theorem exists_seedBridgePair_logSlope :
    ∃ B : SeedBridgePair, ∀ r, 0 < r →
      (3 / 4 : ℝ) * B.profile r ≤ r * deriv B.profile r := by
  obtain ⟨K⟩ := exists_positiveSeedBridge
  let W := connectorProfile K.slope 0 0
  let U := connectorHeight K.slope 0 0
  let cL := exp (connectorLogProfile K.slope 0 0 (K.left - 2))
  let cR := exp (connectorLogProfile K.slope 0 0 (K.right + 2))
  let aL := exp (connectorLogHeight K.slope 0 0 (K.left - 2) - (-2) * (K.left - 2))
  let aR := exp (connectorLogHeight K.slope 0 0 (K.right + 2) - 2 * (K.right + 2))
  refine ⟨⟨W, U, exp (K.left - 1), exp (K.right + 1), exp_pos _,
    exp_lt_exp.mpr (by linarith [K.left_neg, K.right_pos]),
    connectorProfile_contDiffOn K.smooth K.below_four 0 0,
    connectorHeight_contDiffOn K.smooth 0 0,
    fun r hr => connectorProfile_pos _ _ _ hr,
    fun r hr => K.positive_bridge_profile_deriv 0 0 hr,
    fun r hr => radialJacobi_connector K.smooth K.below_four 0 0 0 hr,
    cL, cR, aL, aR, exp_pos _, exp_pos _, exp_pos _, exp_pos _, ?_, ?_⟩, ?_⟩
  · intro r hr hrl
    have hlog : log r < K.left - 1 := by
      simpa only [log_exp] using log_lt_log hr hrl
    constructor
    · let y₁ := min (log r) (K.left - 2) - 1
      exact connectorProfile_eq_cone_of_const (y₁ := y₁) (y₂ := K.left - 1)
        K.smooth K.below_four (fun y hy => K.left_cone y hy.2.le)
        (by norm_num) 0 0
        ⟨by dsimp only [y₁]; linarith [min_le_right (log r) (K.left - 2)], by linarith⟩
        ⟨by dsimp only [y₁]; linarith [min_le_left (log r) (K.left - 2)], hlog⟩
    · exact connectorHeight_eq_power_of_const K.smooth isOpen_Iio
        (convex_Iio (K.left - 1)).isPreconnected (fun y hy => K.left_cone y hy.le)
        0 0 (show K.left - 2 < K.left - 1 by linarith) hr hlog
  · intro r hrl
    have hr : 0 < r := (exp_pos (K.right + 1)).trans hrl
    have hlog : K.right + 1 < log r := by
      simpa only [log_exp] using log_lt_log (exp_pos _) hrl
    constructor
    · let y₂ := max (log r) (K.right + 2) + 1
      exact connectorProfile_eq_cone_of_const (y₁ := K.right + 1) (y₂ := y₂)
        K.smooth K.below_four (fun y hy => K.right_cone y hy.1.le)
        (by norm_num) 0 0
        ⟨by linarith, by dsimp only [y₂]; linarith [le_max_right (log r) (K.right + 2)]⟩
        ⟨hlog, by dsimp only [y₂]; linarith [le_max_left (log r) (K.right + 2)]⟩
    · exact connectorHeight_eq_power_of_const K.smooth isOpen_Ioi
        (convex_Ioi (K.right + 1)).isPreconnected (fun y hy => K.right_cone y hy.le)
        0 0 (show K.right + 1 < K.right + 2 by linarith) hr hlog
  · intro r hr
    exact connectorProfile_logSlope_lower K.smooth K.below_four 0 0 hr
      (K.positive_bridge (log r))

theorem exists_seedBridgePair : Nonempty SeedBridgePair := by
  obtain ⟨B, _⟩ := exists_seedBridgePair_logSlope
  exact ⟨B⟩

end ContinuousFlexibility.Radial
