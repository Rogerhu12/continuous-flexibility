import ContinuousFlexibility.Radial.SeedCentralHeads

/-!
# Prescribing the retained central model window

The cutoff construction accepts arbitrary logarithmic endpoints.  We retain
that freedom when packaging its output as a central cutoff, so the physical
central profile and its kernel can be fixed before choosing the size of the
connected reference.  Both model scale and kernel amplitude remain one.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff

/-- An actual central cutoff can retain any prescribed logarithmic window,
in addition to both central turning points. -/
theorem exists_seedCentralCutoff_retaining (lower upper : ℝ) :
    ∃ K : SeedCentralCutoff, K.left < lower ∧ upper < K.right := by
  let a := log (centralRadius (-sqrt centralOscillatorA))
  let b := log (centralRadius (sqrt centralOscillatorA))
  obtain ⟨K⟩ := exists_seedSlopeCutoff contDiff_centralSeedLogSlope
    (fun y => (centralSeedLogSlope_lt_two y).trans (by norm_num))
    (by norm_num : (2 : ℝ) ^ 2 = 4)
    (by norm_num : (-2 : ℝ) ^ 2 = 4)
    centralSeedLogSlope_log_C1_left centralSeedLogSlope_log_C1_right
    (min a lower) (max b upper)
  let K' : SeedCentralCutoff :=
    { left := K.left
      right := K.right
      slope := K.slope
      left_neg := K.left_neg
      right_pos := K.right_pos
      left_turn := K.left_turn.trans_le (min_le_left a lower)
      right_turn := (le_max_left b upper).trans_lt K.right_turn
      smooth := K.smooth
      below_four := K.below_four
      retained := K.retained
      left_cone := K.left_cone
      right_cone := K.right_cone
      positive_left := K.positive_left
      positive_right := K.positive_right }
  exact ⟨K', K.left_turn.trans_le (min_le_right a lower),
    (le_max_right b upper).trans_lt K.right_turn⟩

/-- Choose the central cutoff after a finite model-coordinate window has
been specified.  The entire closed window is strictly inside the retained
physical patch. -/
theorem exists_seedCentralCutoff_model_window (T : ℝ) :
    ∃ K : SeedCentralCutoff,
      exp K.left < centralRadius (-T) ∧
      centralRadius T < exp K.right ∧
      ∀ x ∈ Icc (-T) T,
        centralRadius x ∈ Ioo (exp K.left) (exp K.right) ∧
        K.profile (centralRadius x) = centralRadialProfile 1 (centralRadius x) ∧
        K.height (centralRadius x) = centralKernelHeight (centralRadius x) := by
  obtain ⟨K, hL, hR⟩ := exists_seedCentralCutoff_retaining
    (log (centralRadius (-T))) (log (centralRadius T))
  have hleft : exp K.left < centralRadius (-T) := by
    simpa only [exp_log (centralRadius_pos _)] using exp_lt_exp.mpr hL
  have hright : centralRadius T < exp K.right := by
    simpa only [exp_log (centralRadius_pos _)] using exp_lt_exp.mpr hR
  refine ⟨K, hleft, hright, ?_⟩
  intro x hx
  have hr : centralRadius x ∈ Ioo (exp K.left) (exp K.right) :=
    ⟨hleft.trans_le (strictMono_centralRadius.monotone hx.1),
      (strictMono_centralRadius.monotone hx.2).trans_lt hright⟩
  exact ⟨hr, K.profile_retained hr, K.height_retained hr⟩

end ContinuousFlexibility.Radial
