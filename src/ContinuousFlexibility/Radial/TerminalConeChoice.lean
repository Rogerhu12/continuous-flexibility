module

public import ContinuousFlexibility.Radial.TerminalConeLayer

/-!
# Choosing one retained-cone length for the finite first band

The upper frequency bound and desired relative error are fixed before
the length. The same choice controls every real frequency in [2,J],
so there is no per-frequency change of the reference geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

theorem exists_terminalCone_length_budget {J ε : ℝ} (hJ : 0 < J) (hε : 0 < ε) :
    ∃ H : ℝ, 2 * log 2 < H ∧ 0 < H ∧ ∀ j : ℝ, 2 ≤ j → j ≤ J →
      terminalConeSourceConstant * exp (-(j * H / 2)) ≤ sqrt (1 / j) * ε ∧
      (1 / j) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-(j * H)) ≤
        (1 / j) * ε := by
  let C := max terminalConeSourceConstant (2 * terminalPhysicalCutoffJetConstant 1 ^ 2)
  have hC : 0 ≤ C := terminalConeSourceConstant_nonneg.trans (le_max_left _ _)
  have hCp : 0 < C + 1 := by linarith only [hC]
  let δ := min (ε * sqrt (1 / J) / (C + 1)) (ε / (C + 1))
  have hδ : 0 < δ := lt_min
    (div_pos (mul_pos hε (sqrt_pos.mpr (one_div_pos.mpr hJ))) hCp) (div_pos hε hCp)
  let H := max (2 * log 2 + 1) (-log δ)
  have hH : 2 * log 2 < H :=
    (by linarith : 2 * log 2 < 2 * log 2 + 1).trans_le (le_max_left _ _)
  have hHpos : 0 < H :=
    (mul_nonneg (by norm_num) (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))).trans_lt hH
  have hexp : exp (-H) ≤ δ := by
    calc
      _ ≤ exp (log δ) := exp_le_exp.mpr (by have := le_max_right (2 * log 2 + 1) (-log δ); linarith)
      _ = _ := exp_log hδ
  have hsource : terminalConeSourceConstant * exp (-H) ≤ ε * sqrt (1 / J) := by
    calc
      _ ≤ C * δ := mul_le_mul (le_max_left _ _) hexp (exp_pos _).le hC
      _ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ ≤ (C + 1) * (ε * sqrt (1 / J) / (C + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hCp.le
      _ = _ := by field_simp [hCp.ne'] <;> ring
  have henergy : (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-H) ≤ ε := by
    calc
      _ ≤ C * δ := mul_le_mul (le_max_right _ _) hexp (exp_pos _).le hC
      _ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ ≤ (C + 1) * (ε / (C + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hCp.le
      _ = _ := by field_simp [hCp.ne'] <;> ring
  refine ⟨H, hH, hHpos, ?_⟩
  intro j hj hjJ
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have hpower : exp (-(j * H / 2)) ≤ exp (-H) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj) hHpos.le]
  have hpower₂ : exp (-(j * H)) ≤ exp (-H) := by
    apply exp_le_exp.mpr
    have hj1 : 1 ≤ j := le_trans (by norm_num) hj
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj1) hHpos.le]
  constructor
  · calc
      _ ≤ terminalConeSourceConstant * exp (-H) :=
        mul_le_mul_of_nonneg_left hpower terminalConeSourceConstant_nonneg
      _ ≤ ε * sqrt (1 / J) := hsource
      _ ≤ ε * sqrt (1 / j) := mul_le_mul_of_nonneg_left
        (sqrt_le_sqrt (one_div_le_one_div_of_le hjpos hjJ)) hε.le
      _ = _ := mul_comm _ _
  · calc
      _ ≤ (1 / j) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-H) :=
        mul_le_mul_of_nonneg_left hpower₂ (by positivity)
      _ = (1 / j) * ((2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-H)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (one_div_nonneg.mpr hjpos.le)

end ContinuousFlexibility.Radial
