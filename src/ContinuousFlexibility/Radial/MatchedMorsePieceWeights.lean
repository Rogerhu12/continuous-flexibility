import ContinuousFlexibility.Radial.InnerMorseInnerWeightCosts

/-!
# The actual piece weight compared with its original cell value

Every constant gap value is one cut value of its larger-index adjacent
model. Consequently both reciprocal signs of the original interpolated
weight cost only half a coefficient power on every actual piece.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

theorem matchedMorse_gap_adjacent_model (N K : ℕ) (hK : 0 < K) (a γ : ℝ)
    (g : Fin (2 * K + 2)) :
    ∃ p : Fin (2 * K + 1), ∃ i : Fin 2,
      innerMorseInnerModelIndex N K p = innerMorseInnerGapIndex N K g ∧
        innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ =
          innerMorseInnerModelWeight N K a γ p i := by
  by_cases hg₀ : g.val = 0
  · have he : g = 0 := Fin.ext hg₀
    subst g
    refine ⟨0, 0, ?_, ?_⟩
    · simp only [innerMorseInnerModelIndex, innerMorseInnerGapIndex, Fin.val_zero,
        hK, ite_true, Nat.zero_le, Nat.sub_zero, Nat.min_eq_left (Nat.sub_le K 1)]
    · rw [innerMorseInnerCutWeight, innerModelChainCuts_gap_right,
        dif_pos (show (0 : Fin (2 * K + 2)).val < 2 * K + 1 by simp)]
      rfl
  have hgpos : 0 < g.val := Nat.pos_of_ne_zero hg₀
  by_cases hg : g.val ≤ K
  · let p : Fin (2 * K + 1) := ⟨g.val - 1, by omega⟩
    have hp : p.val < K := by dsimp only [p]; omega
    have hmin : K - g.val ≤ K - 1 := by omega
    refine ⟨p, 1, ?_, ?_⟩
    · simp only [innerMorseInnerModelIndex, hp, ite_true, innerMorseInnerGapIndex,
        hg, Nat.min_eq_right hmin, p]
      omega
    · rw [← innerMorseInnerCutWeight_gap, innerMorseInnerCutWeight,
        innerModelChainCuts_gap_left, dif_pos hgpos]
  · by_cases hlast : g.val < 2 * K + 1
    · let p : Fin (2 * K + 1) := ⟨g.val, hlast⟩
      have hp : ¬p.val < K := by dsimp only [p]; omega
      have hp₀ : p.val ≠ K := by dsimp only [p]; omega
      have hmin : g.val - K - 1 ≤ K - 1 := by omega
      refine ⟨p, 0, ?_, ?_⟩
      · simp only [innerMorseInnerModelIndex, hp, hp₀, ite_false, innerMorseInnerGapIndex,
          hg, Nat.min_eq_right hmin, p]
      · rw [innerMorseInnerCutWeight, innerModelChainCuts_gap_right, dif_pos hlast]
    · let p : Fin (2 * K + 1) := ⟨g.val - 1, by omega⟩
      have he : g.val = 2 * K + 1 := by omega
      have hp : ¬p.val < K := by dsimp only [p]; omega
      have hp₀ : p.val ≠ K := by dsimp only [p]; omega
      have hmin : K - 1 ≤ g.val - K - 1 := by omega
      refine ⟨p, 1, ?_, ?_⟩
      · simp only [innerMorseInnerModelIndex, hp, hp₀, ite_false, innerMorseInnerGapIndex,
          hg, Nat.min_eq_left hmin, p]
        omega
      · rw [← innerMorseInnerCutWeight_gap, innerMorseInnerCutWeight,
          innerModelChainCuts_gap_left, dif_pos hgpos]

theorem matchedMorse_modelCut_log_bound (N K : ℕ) {a γ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    (p : Fin (2 * K + 1)) (i : Fin 2) :
    |log (innerMorseInnerModelWeight N K a γ p i /
      innerCellWeight N a γ (innerMorseInnerModelIndex N K p))| ≤
        (1 / 2 : ℝ) * radialQ (innerMorseInnerModelIndex N K p) := by
  by_cases hp : p.val < K
  · simp only [innerMorseInnerModelWeight, innerMorseInnerModelIndex, hp, ite_true]
    exact innerMorseCutWeight_log_bound N ha hγ hN hNa (Nat.le_add_right _ _) false i
  · by_cases hp₀ : p.val = K
    · simp only [innerMorseInnerModelWeight, innerMorseInnerModelIndex, hp, hp₀,
        lt_self_iff_false, ite_false, ite_true, innerCellWeight_base, div_one, log_one,
        abs_zero]
      exact mul_nonneg (by norm_num) (radialQ_nonneg N)
    · simp only [innerMorseInnerModelWeight, innerMorseInnerModelIndex, hp, hp₀, ite_false]
      exact innerMorseCutWeight_log_bound N ha hγ hN hNa (Nat.le_add_right _ _) true i

theorem matchedMorse_signed_log_bound {u v B σ : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hσ : |σ| ≤ 1) (hlog : |log (u / v)| ≤ B) :
    |log (u ^ σ / v ^ σ)| ≤ B := by
  have he : log (u ^ σ / v ^ σ) = σ * log (u / v) := by
    rw [log_div (rpow_pos_of_pos hu σ).ne' (rpow_pos_of_pos hv σ).ne',
      log_rpow hu, log_rpow hv, log_div hu.ne' hv.ne']
    ring
  rw [he, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hσ).trans hlog

section ActualPiece

variable {D : ReferenceData} (N K : ℕ) (hK : 0 < K) {a γ σ : ℝ}
  (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
  (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)

include hK ha hγ hσ hN hNa

theorem matchedMorse_actual_piece_log_bound
    (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hx : x ∈ Ioo (G.left p) (G.right p)) :
    |log ((innerMorseInnerWeight N K a γ G l r x) ^ σ /
      (innerCellWeight N a γ (innerMorseInnerPieceIndex N K p)) ^ σ)| ≤
        (1 / 2 : ℝ) * radialQ (innerMorseInnerPieceIndex N K p) := by
  rcases innerModelChainPiece_or_gap p with ⟨p, rfl⟩ | ⟨g, rfl⟩
  · rw [innerMorseInnerPieceIndex_model,
      innerMorseInnerWeight_on_model N K a γ G l r p ⟨hx.1, hx.2.le⟩]
    exact (innerInterpolatedWeight_signed_abs_log_ratio_le _ _
      (innerMorseInnerModelWeight_pos N K a γ p 0)
      (innerMorseInnerModelWeight_pos N K a γ p 1)
      (innerCellWeight_pos N a γ _) hσ x).trans
      (max_le (matchedMorse_modelCut_log_bound N K ha hγ hN hNa p 0)
        (matchedMorse_modelCut_log_bound N K ha hγ hN hNa p 1))
  · rw [innerMorseInnerPieceIndex_gap,
      innerMorseInnerWeight_on_gap N K a γ G l r g ⟨hx.1, hx.2.le⟩]
    obtain ⟨p, i, hi, hw⟩ := matchedMorse_gap_adjacent_model N K hK a γ g
    rw [hw, ← hi]
    exact matchedMorse_signed_log_bound
      (innerMorseInnerModelWeight_pos N K a γ p i)
      (innerCellWeight_pos N a γ _) hσ
      (matchedMorse_modelCut_log_bound N K ha hγ hN hNa p i)

end ActualPiece

/-- Both signs of the actual weight and the inverse of the actual
loss-times-weight have a common fixed coefficient exponent 38. -/
theorem matchedMorse_actual_piece_exp_bounds
    {D : ReferenceData} (N K : ℕ) (hK : 0 < K) (hN : 4096 ≤ N)
    (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
    (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)
    {σ : ℝ} (hσ : |σ| ≤ 1)
    (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hx : x ∈ Ioo (G.left p) (G.right p)) :
    |(innerMorseInnerWeight N K 0 1 G l r x) ^ σ| ≤
        exp (radialS N) * exp (38 * radialQ (innerMorseInnerPieceIndex N K p) +
          σ * radialS (innerMorseInnerPieceIndex N K p)) ∧
      |(innerMorseInnerLoss N K G 37 x *
          (innerMorseInnerWeight N K 0 1 G l r x) ^ σ)⁻¹| ≤
        exp (radialS N) * exp (38 * radialQ (innerMorseInnerPieceIndex N K p) -
          σ * radialS (innerMorseInnerPieceIndex N K p)) := by
  let m := innerMorseInnerPieceIndex N K p
  let W := (innerMorseInnerWeight N K 0 1 G l r x) ^ σ
  have hW : 0 < W := rpow_pos_of_pos (innerMorseInnerWeight_pos N K 0 1 G l r x) σ
  have hh := matchedMorse_actual_piece_log_bound N K hK
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : |(1 : ℝ)| ≤ 1) hσ hN
    (by simpa only [mul_zero] using (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))) G l r p hx
  rw [log_div hW.ne' (rpow_pos_of_pos (innerCellWeight_pos N 0 1 m) σ).ne',
    log_rpow (innerCellWeight_pos N 0 1 m), innerCellWeight_log] at hh
  simp only [zero_mul, one_mul, zero_add] at hh
  have hlo := (abs_le.mp hh).1
  have hhi := (abs_le.mp hh).2
  have hS₀ : 0 ≤ radialS N := by unfold radialS; positivity
  have hσlo := mul_le_mul_of_nonneg_right (abs_le.mp hσ).1 hS₀
  have hσhi := mul_le_mul_of_nonneg_right (abs_le.mp hσ).2 hS₀
  have hQ := radialQ_nonneg m
  have hQN := radialQ_nonneg N
  constructor
  · rw [abs_of_pos hW, ← exp_log hW, ← exp_add]
    apply exp_le_exp.mpr
    change log W ≤ radialS N + (38 * radialQ m + σ * radialS m)
    nlinarith only [hhi, hσlo, hQ]
  · rw [innerMorseInnerLoss_on_piece N K G 37 p hx, innerCoefficientLoss_eq_exp]
    have he : (exp (-(37 * (radialQ m - radialQ N))) * W)⁻¹ =
        exp (37 * (radialQ m - radialQ N) - log W) := by
      calc
        _ = exp (37 * (radialQ m - radialQ N)) * W⁻¹ := by
          rw [mul_inv_rev, ← exp_neg, neg_neg]
          ring
        _ = exp (37 * (radialQ m - radialQ N)) * exp (-log W) := by
          rw [exp_neg, exp_log hW]
        _ = _ := by
          rw [← exp_add]
          congr 1
    rw [he, abs_of_pos (exp_pos _), ← exp_add]
    apply exp_le_exp.mpr
    change 37 * (radialQ m - radialQ N) - log W ≤
      radialS N + (38 * radialQ m - σ * radialS m)
    nlinarith only [hlo, hσhi, hQ, hQN]

end ContinuousFlexibility.Radial
