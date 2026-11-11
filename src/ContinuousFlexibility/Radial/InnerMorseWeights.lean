import ContinuousFlexibility.Radial.InnerCoefficientWeights

/-!
# The prescribed weights on both retained Morse tails

The same cell value is used on the two tails. Physical left and right
cut values are the neighboring geometric means in the appropriate
order. The first inward value is the middle value one. The actual smooth
interpolation has fixed coefficient-power comparisons both with the
cell value and with either cut, for both reciprocal weight signs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def innerMorseInwardWeight (N : ℕ) (a γ : ℝ) (m : ℕ) : ℝ :=
  if m = N then 1 else
    innerGeometricMeanWeight (innerCellWeight N a γ (m - 1)) (innerCellWeight N a γ m)

def innerMorseOutwardWeight (N : ℕ) (a γ : ℝ) (m : ℕ) : ℝ :=
  innerGeometricMeanWeight (innerCellWeight N a γ m) (innerCellWeight N a γ (m + 1))

/-- The tail side changes the order of the two physical endpoint
weights, not the coordinate direction or the cell coefficient. -/
def innerMorseCutWeight (N : ℕ) (a γ : ℝ) (side : Bool) (m : ℕ) (i : Fin 2) : ℝ :=
  if side then
    if i = 0 then innerMorseInwardWeight N a γ m else innerMorseOutwardWeight N a γ m
  else
    if i = 0 then innerMorseOutwardWeight N a γ m else innerMorseInwardWeight N a γ m

theorem innerMorseCutWeight_pos (N : ℕ) (a γ : ℝ) (side : Bool) (m : ℕ) (i : Fin 2) :
    0 < innerMorseCutWeight N a γ side m i := by
  have hi : 0 < innerMorseInwardWeight N a γ m := by
    unfold innerMorseInwardWeight
    split_ifs
    · norm_num
    · exact innerGeometricMeanWeight_pos (innerCellWeight_pos N a γ _)
        (innerCellWeight_pos N a γ _)
  have ho : 0 < innerMorseOutwardWeight N a γ m :=
    innerGeometricMeanWeight_pos (innerCellWeight_pos N a γ _) (innerCellWeight_pos N a γ _)
  unfold innerMorseCutWeight
  split_ifs <;> assumption

theorem innerMorseCutWeight_log_bound (N : ℕ) {a γ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    {m : ℕ} (hm : N ≤ m) (side : Bool) (i : Fin 2) :
    |log (innerMorseCutWeight N a γ side m i / innerCellWeight N a γ m)| ≤
      (1 / 2 : ℝ) * radialQ m := by
  have hadj (k : ℕ) (hk : N ≤ k) :
      |log (innerCellWeight N a γ (k + 1) / innerCellWeight N a γ k)| ≤ radialQ k := by
    simpa only [rpow_one] using innerCellWeight_signed_log_adjacent_fixed N ha hγ
      (by norm_num : |(1 : ℝ)| ≤ 1) (hN.trans hk)
      (hNa.trans (by exact_mod_cast hk))
  have hi : |log (innerMorseInwardWeight N a γ m / innerCellWeight N a γ m)| ≤
      (1 / 2 : ℝ) * radialQ m := by
    by_cases heq : m = N
    · subst m
      simpa only [innerMorseInwardWeight, eq_self_iff_true, ite_true, innerCellWeight_base,
        div_one, log_one, abs_zero] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (radialQ_nonneg N)
    · have hprev : N ≤ m - 1 := by omega
      have hsucc : m - 1 + 1 = m := by omega
      rw [innerMorseInwardWeight, if_neg heq]
      have he := innerGeometricMeanWeight_abs_log_ratio
        (innerCellWeight_pos N a γ (m - 1)) (innerCellWeight_pos N a γ m) true
      simp only [ite_true] at he
      rw [he]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have h := hadj (m - 1) hprev
      rw [hsucc] at h
      exact h.trans (radialQ_monotone (Nat.sub_le m 1))
  have ho : |log (innerMorseOutwardWeight N a γ m / innerCellWeight N a γ m)| ≤
      (1 / 2 : ℝ) * radialQ m := by
    have he := innerGeometricMeanWeight_abs_log_ratio
      (innerCellWeight_pos N a γ m) (innerCellWeight_pos N a γ (m + 1)) false
    simp only [Bool.false_eq_true, ite_false] at he
    rw [innerMorseOutwardWeight, he]
    exact mul_le_mul_of_nonneg_left (hadj m hm) (by norm_num)
  unfold innerMorseCutWeight
  split_ifs <;> assumption

def innerMorseInterpolatedWeight (N : ℕ) (a γ : ℝ) (side : Bool)
    (m : ℕ) (l r : ℝ) : ℝ → ℝ :=
  innerInterpolatedWeight l r (innerMorseCutWeight N a γ side m 0)
    (innerMorseCutWeight N a γ side m 1)

theorem innerMorseInterpolatedWeight_cell_log_bound (N : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) {m : ℕ} (hm : N ≤ m)
    (side : Bool) (l r x : ℝ) :
    |log ((innerMorseInterpolatedWeight N a γ side m l r x) ^ σ /
      (innerCellWeight N a γ m) ^ σ)| ≤ (1 / 2 : ℝ) * radialQ m := by
  apply (innerInterpolatedWeight_signed_abs_log_ratio_le l r
    (innerMorseCutWeight_pos N a γ side m 0) (innerMorseCutWeight_pos N a γ side m 1)
    (innerCellWeight_pos N a γ m) hσ x).trans
  exact max_le (innerMorseCutWeight_log_bound N ha hγ hN hNa hm side 0)
    (innerMorseCutWeight_log_bound N ha hγ hN hNa hm side 1)

theorem inner_abs_log_ratio_via_base {u v b A B : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hb : 0 < b)
    (huB : |log (u / b)| ≤ A) (hvB : |log (v / b)| ≤ B) :
    |log (u / v)| ≤ A + B := by
  have hlog : log (u / v) = log (u / b) - log (v / b) := by
    rw [log_div hu.ne' hv.ne', log_div hu.ne' hb.ne', log_div hv.ne' hb.ne']
    ring
  rw [hlog]
  have htriangle : |log (u / b) - log (v / b)| ≤ |log (u / b)| + |log (v / b)| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (log (u / b)) (-log (v / b))
  exact htriangle.trans (add_le_add huB hvB)

/-- The full model interpolation differs from either buffer weight by
at most one fixed coefficient power, for each weight sign. -/
theorem innerMorseInterpolatedWeight_cut_ratios (N : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) {m : ℕ} (hm : N ≤ m)
    (side : Bool) (l r x : ℝ) (i : Fin 2) :
    (innerMorseInterpolatedWeight N a γ side m l r x) ^ σ /
        (innerMorseCutWeight N a γ side m i) ^ σ ≤ radialE m ∧
      (innerMorseCutWeight N a γ side m i) ^ σ /
        (innerMorseInterpolatedWeight N a γ side m l r x) ^ σ ≤ radialE m := by
  have hw := innerInterpolatedWeight_pos l r
    (innerMorseCutWeight N a γ side m 0) (innerMorseCutWeight N a γ side m 1) x
  have hcut := innerMorseCutWeight_pos N a γ side m i
  have hcell := innerCellWeight_pos N a γ m
  have hc : |log ((innerMorseCutWeight N a γ side m i) ^ σ /
      (innerCellWeight N a γ m) ^ σ)| ≤ (1 / 2 : ℝ) * radialQ m := by
    have heq : log ((innerMorseCutWeight N a γ side m i) ^ σ /
        (innerCellWeight N a γ m) ^ σ) =
        σ * log (innerMorseCutWeight N a γ side m i / innerCellWeight N a γ m) := by
      rw [log_div (rpow_pos_of_pos hcut σ).ne' (rpow_pos_of_pos hcell σ).ne',
        log_rpow hcut, log_rpow hcell, log_div hcut.ne' hcell.ne']
      ring
    rw [heq, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hσ).trans
      (innerMorseCutWeight_log_bound N ha hγ hN hNa hm side i)
  have hlog := inner_abs_log_ratio_via_base (rpow_pos_of_pos hw σ)
    (rpow_pos_of_pos hcut σ) (rpow_pos_of_pos hcell σ)
    (innerMorseInterpolatedWeight_cell_log_bound N ha hγ hσ hN hNa hm side l r x) hc
  have hlog' : |log ((innerMorseInterpolatedWeight N a γ side m l r x) ^ σ /
      (innerMorseCutWeight N a γ side m i) ^ σ)| ≤ 1 * radialQ m := by
    simpa only [show (1 / 2 : ℝ) * radialQ m + (1 / 2 : ℝ) * radialQ m =
      1 * radialQ m by ring] using hlog
  simpa only [rpow_one] using inner_ratios_le_coefficient_of_abs_log
    (rpow_pos_of_pos hw σ) (rpow_pos_of_pos hcut σ) m hlog'

end ContinuousFlexibility.Radial
