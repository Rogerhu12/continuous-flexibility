module

public import ContinuousFlexibility.Radial.TerminalConeChoice

/-!
# One first-band length after its inverse bound and selected margin

The inverse norm bound is fixed before this choice. A single small
coefficient controls both actual cutoff errors, and one retained-cone
length realizes that coefficient throughout the finite first band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real

theorem exists_terminalCone_matching_budget {J margin inverseCost : ℝ}
    (hJ : 0 < J) (hm : 0 < margin) (hG : 0 ≤ inverseCost) :
    ∃ ε H : ℝ, 0 < ε ∧ 2 * log 2 < H ∧ 0 < H ∧
      ε + inverseCost * ε ^ 2 ≤ margin / 16 ∧
      ∀ j : ℝ, 2 ≤ j → j ≤ J →
        terminalConeSourceConstant * exp (-(j * H / 2)) ≤ sqrt (1 / j) * ε ∧
        (1 / j) * (2 * terminalPhysicalCutoffJetConstant 1 ^ 2) * exp (-(j * H)) ≤
          (1 / j) * ε := by
  let ε := min 1 (margin / (32 * (inverseCost + 1)))
  have hK : 0 < inverseCost + 1 := by linarith only [hG]
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hm (by positivity))
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hsquare : ε ^ 2 ≤ ε := by nlinarith only [hε.le, hε₁]
  have hscaled : (inverseCost + 1) * ε ≤ margin / 32 := by
    calc
      _ ≤ (inverseCost + 1) * (margin / (32 * (inverseCost + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = _ := by field_simp [hK.ne'] <;> ring
  have hbudget : ε + inverseCost * ε ^ 2 ≤ margin / 16 := by
    have hsq := mul_le_mul_of_nonneg_left hsquare hG
    nlinarith only [hsq, hscaled, hm.le]
  obtain ⟨H, hH, hHpos, hbounds⟩ := exists_terminalCone_length_budget hJ hε
  exact ⟨ε, H, hε, hH, hHpos, hbudget, hbounds⟩

end ContinuousFlexibility.Radial
