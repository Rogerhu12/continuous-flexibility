import ContinuousFlexibility.Radial.InnerMorseInnerWeights
import ContinuousFlexibility.Radial.MatchingGraphRestrictions

/-!
# The actual finite-chain weight on terminal caps

Both physical terminal gaps carry the same original geometric-mean cut
weight. The half-open partition is kept unchanged: its possible different
value at the left cut is removed only by the proved physical null-set
lemma. The exponential bound retains the exact signed height exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements

theorem innerMorseInnerOuterWeight_eq_inward (N K : ℕ) (a γ : ℝ) :
    innerMorseInnerOuterWeight N K a γ = innerMorseInwardWeight N a γ (N + K) := by
  by_cases hK : K = 0
  · subst K
    simp [innerMorseInnerOuterWeight, innerMorseInwardWeight]
  · have hne : N + K ≠ N := by omega
    have hpred : N + K - 1 = N + (K - 1) := by omega
    have hsucc : N + (K - 1) + 1 = N + K := by omega
    simp only [innerMorseInnerOuterWeight, hK, ite_false, innerMorseInwardWeight,
      hne, innerMorseOutwardWeight, hpred, hsucc]

/-- The actual terminal cut has the same half-coefficient comparison
as every original Morse cut, for both reciprocal weight signs. -/
theorem innerMorseInnerOuterWeight_signed_log_bound (N K : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) :
    |log ((innerMorseInnerOuterWeight N K a γ) ^ σ /
      (innerCellWeight N a γ (N + K)) ^ σ)| ≤ (1 / 2 : ℝ) * radialQ (N + K) := by
  have ho := innerMorseInnerOuterWeight_pos N K a γ
  have hc := innerCellWeight_pos N a γ (N + K)
  have hraw : |log (innerMorseInnerOuterWeight N K a γ /
      innerCellWeight N a γ (N + K))| ≤ (1 / 2 : ℝ) * radialQ (N + K) := by
    rw [innerMorseInnerOuterWeight_eq_inward]
    simpa only [innerMorseCutWeight, eq_self_iff_true, ite_true] using
      innerMorseCutWeight_log_bound N ha hγ hN hNa
        (Nat.le_add_right N K) true (0 : Fin 2)
  have heq : log ((innerMorseInnerOuterWeight N K a γ) ^ σ /
      (innerCellWeight N a γ (N + K)) ^ σ) =
      σ * log (innerMorseInnerOuterWeight N K a γ / innerCellWeight N a γ (N + K)) := by
    rw [log_div (rpow_pos_of_pos ho σ).ne' (rpow_pos_of_pos hc σ).ne',
      log_rpow ho, log_rpow hc, log_div ho.ne' hc.ne']
    ring
  rw [heq, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hσ).trans hraw

/-- The base-index constant is uniform over the finite-chain length,
the weight sign and all attenuation exponents of absolute value at most one. -/
theorem innerMorseInnerOuterWeight_exp_bound (N K : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) :
    |(innerMorseInnerOuterWeight N K a γ) ^ σ| ≤
      exp (a * radialQ N + radialS N) *
        exp ((a + 1 / 2) * radialQ (N + K) + (σ * γ) * radialS (N + K)) := by
  have ho := rpow_pos_of_pos (innerMorseInnerOuterWeight_pos N K a γ) σ
  have hc := rpow_pos_of_pos (innerCellWeight_pos N a γ (N + K)) σ
  have hh := (abs_le.mp (innerMorseInnerOuterWeight_signed_log_bound N K
    ha hγ hσ hN hNa)).2
  rw [log_div ho.ne' hc.ne', log_rpow (innerCellWeight_pos N a γ (N + K)),
    innerCellWeight_log] at hh
  have hσhi := (abs_le.mp hσ).2
  have hσlo : -σ ≤ 1 := by linarith only [(abs_le.mp hσ).1]
  have hσγ : |σ * γ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hσ hγ (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hσγlo : -(σ * γ) ≤ 1 := by linarith only [(abs_le.mp hσγ).1]
  have hS : 0 ≤ radialS N := by unfold radialS; positivity
  have h₁ := mul_le_mul_of_nonneg_right hσhi
    (mul_nonneg ha (radialQ_nonneg (N + K)))
  have h₂ := mul_le_mul_of_nonneg_right hσlo (mul_nonneg ha (radialQ_nonneg N))
  have h₃ := mul_le_mul_of_nonneg_right hσγlo hS
  have hlog : log ((innerMorseInnerOuterWeight N K a γ) ^ σ) ≤
      (a * radialQ N + radialS N) +
        ((a + 1 / 2) * radialQ (N + K) + (σ * γ) * radialS (N + K)) := by
    nlinarith only [hh, h₁, h₂, h₃]
  rw [abs_of_pos ho, ← exp_log ho]
  exact (exp_le_exp.mpr hlog).trans_eq (exp_add _ _)

section PhysicalWeight

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)

/-- Both terminal gaps have the original outer cut weight. -/
theorem innerMorseInnerWeight_on_terminal_gap (right : Bool) {x : ℝ}
    (hx : x ∈ Ioc
      (G.left (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0)))
      (G.right (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0)))) :
    innerMorseInnerWeight N K a γ G l r x = innerMorseInnerOuterWeight N K a γ := by
  rw [innerMorseInnerWeight_on_gap N K a γ G l r _ hx]
  cases right
  · rw [← innerMorseInnerCutWeight_gap]
    simp only [Bool.false_eq_true, ite_false, innerMorseInnerCutWeight,
      innerModelChainCuts_gap_left, Fin.val_zero, lt_self_iff_false, dite_false]
    exact dif_neg (Nat.lt_irrefl 0)
  · simp only [eq_self_iff_true, ite_true, innerMorseInnerCutWeight,
      innerModelChainCuts_gap_right, Fin.val_last, lt_self_iff_false, dite_false]

/-- A cap in either closed terminal gap has the correct weight almost
everywhere for the original radial Hilbert measure. -/
theorem innerMorseInnerWeight_terminal_cap_ae
    (hD : IsAccumulatingProfile D) (right : Bool) {cap : Set ℝ}
    (hcap : cap ⊆ Icc
      (G.left (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0)))
      (G.right (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0)))) :
    ∀ᵐ x ∂radialHilbertMeasure D, x ∈ cap →
      innerMorseInnerWeight N K a γ G l r x = innerMorseInnerOuterWeight N K a γ := by
  filter_upwards [matching_ae_ne hD
    (G.left (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0)))] with x hx hxc
  have hc := hcap hxc
  exact innerMorseInnerWeight_on_terminal_gap N K a γ G l r right
    ⟨lt_of_le_of_ne hc.1 hx.symm, hc.2⟩

/-- The actual weight on a physical cap, without postulating an
exponential weight comparison as an input. -/
theorem innerMorseInnerWeight_terminal_cap_exp_bound
    (hD : IsAccumulatingProfile D) (right : Bool) {cap : Set ℝ}
    (hcap : cap ⊆ Icc
      (G.left (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0)))
      (G.right (innerModelChainGap (if right then Fin.last (2 * K + 1) else 0))))
    {σ : ℝ} (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) :
    ∀ᵐ x ∂radialHilbertMeasure D, x ∈ cap →
      |(innerMorseInnerWeight N K a γ G l r x) ^ σ| ≤
        exp (a * radialQ N + radialS N) *
          exp ((a + 1 / 2) * radialQ (N + K) + (σ * γ) * radialS (N + K)) := by
  filter_upwards [innerMorseInnerWeight_terminal_cap_ae N K a γ G l r hD right hcap]
    with x hx hxc
  rw [hx hxc]
  exact innerMorseInnerOuterWeight_exp_bound N K ha hγ hσ hN hNa

end PhysicalWeight

end ContinuousFlexibility.Radial
