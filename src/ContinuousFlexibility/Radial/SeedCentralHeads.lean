module

public import ContinuousFlexibility.Radial.SeedCentralPair

/-! # Arbitrarily long exact cone heads of the central seed -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff

namespace SeedCentralCutoff

theorem retained_turns (K : SeedCentralCutoff) :
    0 < exp K.left ∧
      exp K.left < centralRadius (-sqrt centralOscillatorA) ∧
      centralRadius (sqrt centralOscillatorA) < exp K.right := by
  refine ⟨exp_pos _, ?_, ?_⟩
  · simpa only [exp_log (centralRadius_pos _)] using exp_lt_exp.mpr K.left_turn
  · simpa only [exp_log (centralRadius_pos _)] using exp_lt_exp.mpr K.right_turn

theorem profile_retained (K : SeedCentralCutoff) {r : ℝ}
    (hr : r ∈ Ioo (exp K.left) (exp K.right)) :
    K.profile r = centralRadialProfile 1 r := by
  have hp := (exp_pos K.left).trans hr.1
  have hy : log r ∈ Ioo K.left K.right := by
    constructor
    · simpa only [log_exp] using log_lt_log (exp_pos _) hr.1
    · simpa only [log_exp] using log_lt_log hp hr.2
  simpa only [exp_log hp] using K.profile_retained_log hy

theorem height_retained (K : SeedCentralCutoff) {r : ℝ}
    (hr : r ∈ Ioo (exp K.left) (exp K.right)) :
    K.height r = centralKernelHeight r := by
  have hp := (exp_pos K.left).trans hr.1
  have hy : log r ∈ Ioo K.left K.right := by
    constructor
    · simpa only [log_exp] using log_lt_log (exp_pos _) hr.1
    · simpa only [log_exp] using log_lt_log hp hr.2
  simpa only [exp_log hp] using K.height_retained_log hy

/-- The exact cone regions can supply any requested logarithmic length. -/
theorem free_heads (K : SeedCentralCutoff) {required : ℝ} (hreq : 0 < required) :
    ∃ l₁ l₂ h₁ h₂ cL cR : ℝ,
      0 < l₁ ∧ l₁ < l₂ ∧ l₂ < exp K.left ∧
      exp K.right < h₁ ∧ h₁ < h₂ ∧ 0 < cL ∧ 0 < cR ∧
      required ≤ log (l₂ / l₁) ∧ required ≤ log (h₂ / h₁) ∧
      (∀ r ∈ Ioo l₁ l₂, K.profile r = cL * r) ∧
      (∀ r ∈ Ioo h₁ h₂, K.profile r = cR * r) ∧
      (∀ r ∈ Ioo l₂ (exp K.left), 0 < deriv K.profile r) ∧
      (∀ r ∈ Ioo (exp K.right) h₁, 0 < deriv K.profile r) := by
  obtain ⟨cL, cR, aL, aR, hcL, hcR, _, _, hleft, hright⟩ := K.exact_cones
  refine ⟨exp (K.left - required - 3), exp (K.left - 2),
    exp (K.right + 2), exp (K.right + required + 3), cL, cR,
    exp_pos _, exp_lt_exp.mpr (by linarith), exp_lt_exp.mpr (by linarith),
    exp_lt_exp.mpr (by linarith), exp_lt_exp.mpr (by linarith), hcL, hcR,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [log_div (exp_ne_zero _) (exp_ne_zero _), log_exp, log_exp]
    linarith
  · rw [log_div (exp_ne_zero _) (exp_ne_zero _), log_exp, log_exp]
    linarith
  · intro r hr
    have hp := (exp_pos (K.left - required - 3)).trans hr.1
    have hl : log r < K.left - 2 := by
      simpa only [log_exp] using log_lt_log hp hr.2
    exact (hleft r hp (by linarith)).1
  · intro r hr
    have hp := (exp_pos (K.right + 2)).trans hr.1
    have hl : K.right + 2 < log r := by
      simpa only [log_exp] using log_lt_log (exp_pos _) hr.1
    exact (hright r hp (by linarith)).1
  · intro r hr
    have hp := (exp_pos (K.left - 2)).trans hr.1
    apply K.profile_deriv_pos hp
    left
    have hl : log r < K.left := by
      simpa only [log_exp] using log_lt_log hp hr.2
    exact hl.le
  · intro r hr
    have hp := (exp_pos K.right).trans hr.1
    apply K.profile_deriv_pos hp
    right
    have hl : K.right < log r := by
      simpa only [log_exp] using log_lt_log (exp_pos _) hr.1
    exact hl.le

end SeedCentralCutoff
end ContinuousFlexibility.Radial
