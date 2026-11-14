module

public import ContinuousFlexibility.Radial.InnerWeightInterpolation

/-!
# Fixed coefficient powers for the inner weights

The starting index is chosen after the weight exponent. Beyond this
index every adjacent logarithmic ratio is bounded by radialQ m, with
an exponent independent of the weight exponent and of the number of
retained cells. These local bounds, rather than the condition number of
the entire weight, are what enter the two final inner inverse estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

/-- A concrete threshold absorbs both terms of the adjacent-weight
estimate into one fixed coefficient power. -/
theorem inner_weight_adjacent_exponent_le {a : ℝ} {m : ℕ}
    (hm : 4096 ≤ m) (ha : 64 * a ≤ m) :
    32 * (m : ℝ) ^ 2 + 32 * a * (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m) ≤
      radialQ m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog : 1 ≤ log (exp 1 + (m : ℝ)) := ssv_one_le_log hm0
  have hsqrt : (64 : ℝ) ≤ sqrt m := by
    apply (le_sqrt (by norm_num) hm0).mpr
    norm_num only [show (64 : ℝ) ^ 2 = 4096 by norm_num]
    exact_mod_cast hm
  have hprod : (64 : ℝ) ≤ sqrt m * log (exp 1 + m) := by
    simpa only [mul_one] using
      mul_le_mul hsqrt hlog (by norm_num : (0 : ℝ) ≤ 1) (sqrt_nonneg (m : ℝ))
  have hfirst := mul_le_mul_of_nonneg_left hprod (sq_nonneg (m : ℝ))
  have hsecond := mul_le_mul_of_nonneg_right ha
    (mul_nonneg (mul_nonneg hm0 (sqrt_nonneg (m : ℝ))) (zero_le_one.trans hlog))
  rw [ssv_rpow_three_half hm0, radialQ, ssv_rpow_five_half hm0]
  nlinarith only [hfirst, hsecond]

theorem innerCellWeight_signed_log_adjacent_fixed (N : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1) {m : ℕ}
    (hm : 4096 ≤ m) (hma : 64 * a ≤ m) :
    |log ((innerCellWeight N a γ (m + 1)) ^ σ / (innerCellWeight N a γ m) ^ σ)| ≤
      radialQ m :=
  (innerCellWeight_signed_log_adjacent_le N ha hγ hσ (by omega)).trans
    (inner_weight_adjacent_exponent_le hm hma)

/-- The fixed coefficient exponent is available after any previously
chosen lower cutoff. Thus it respects the manuscript's order of choices. -/
theorem exists_innerCellWeight_fixed_exponent (a : ℝ) (initial : ℕ) :
    ∃ N : ℕ, initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (64 * a)
  refine ⟨max initial (max 4096 K), le_max_left _ _, ?_, ?_⟩
  · exact (le_max_left 4096 K).trans (le_max_right initial (max 4096 K))
  · exact hK.trans (by exact_mod_cast
      ((le_max_right 4096 K).trans (le_max_right initial (max 4096 K))))

/-- Interior cells use the same fixed exponent for both signs, despite
the possible large absolute size of their common cell weight. -/
theorem innerInterpolatedWeight_cell_fixed_log_bound
    (N : ℕ) (l r : ℝ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) {m : ℕ} (hm : N < m) (x : ℝ) :
    |log ((innerInterpolatedWeight l r
      (innerGeometricMeanWeight (innerCellWeight N a γ (m - 1)) (innerCellWeight N a γ m))
      (innerGeometricMeanWeight (innerCellWeight N a γ m) (innerCellWeight N a γ (m + 1))) x) ^ σ /
        (innerCellWeight N a γ m) ^ σ)| ≤ (1 / 2 : ℝ) * radialQ m := by
  have hprev : N ≤ m - 1 := by omega
  have hsucc : m - 1 + 1 = m := by omega
  have hleft : |log (innerCellWeight N a γ m / innerCellWeight N a γ (m - 1))| ≤
      radialQ (m - 1) := by
    simpa only [Real.rpow_one, hsucc] using
      innerCellWeight_signed_log_adjacent_fixed N ha hγ
        (by norm_num : |(1 : ℝ)| ≤ 1) (hN.trans hprev)
        (hNa.trans (by exact_mod_cast hprev))
  have hright : |log (innerCellWeight N a γ (m + 1) / innerCellWeight N a γ m)| ≤
      radialQ m := by
    simpa only [Real.rpow_one] using
      innerCellWeight_signed_log_adjacent_fixed N ha hγ
        (by norm_num : |(1 : ℝ)| ≤ 1) (hN.trans hm.le)
        (hNa.trans (by exact_mod_cast hm.le))
  exact (innerInterpolatedWeight_geometric_log_bound l r
    (innerCellWeight_pos N a γ (m - 1)) (innerCellWeight_pos N a γ m)
    (innerCellWeight_pos N a γ (m + 1)) hσ x).trans
      (mul_le_mul_of_nonneg_left
        (max_le (hleft.trans (radialQ_monotone (Nat.sub_le m 1))) hright) (by norm_num))

/-- At the first cell the inward buffer has the finite-middle weight
one. The outward buffer has the same geometric-mean rule as every gap. -/
theorem innerInterpolatedWeight_first_cell_fixed_log_bound
    (N : ℕ) (l r : ℝ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ)) (x : ℝ) :
    |log ((innerInterpolatedWeight l r 1
      (innerGeometricMeanWeight (innerCellWeight N a γ N) (innerCellWeight N a γ (N + 1))) x) ^ σ /
        (innerCellWeight N a γ N) ^ σ)| ≤ (1 / 2 : ℝ) * radialQ N := by
  have hcell := innerCellWeight_pos N a γ N
  have hnext := innerCellWeight_pos N a γ (N + 1)
  have hadj : |log (innerCellWeight N a γ (N + 1) / innerCellWeight N a γ N)| ≤ radialQ N := by
    simpa only [Real.rpow_one] using
      innerCellWeight_signed_log_adjacent_fixed N ha hγ
        (by norm_num : |(1 : ℝ)| ≤ 1) hN hNa
  have hleft : |log (1 / innerCellWeight N a γ N)| = 0 := by
    rw [innerCellWeight_base, div_self (by norm_num : (1 : ℝ) ≠ 0), log_one, abs_zero]
  have hright : |log (innerGeometricMeanWeight (innerCellWeight N a γ N)
      (innerCellWeight N a γ (N + 1)) / innerCellWeight N a γ N)| ≤
        (1 / 2 : ℝ) * radialQ N := by
    have he := innerGeometricMeanWeight_abs_log_ratio hcell hnext false
    simp only [Bool.false_eq_true, ite_false] at he
    rw [he]
    exact mul_le_mul_of_nonneg_left hadj (by norm_num)
  exact (innerInterpolatedWeight_signed_abs_log_ratio_le l r (by norm_num)
    (innerGeometricMeanWeight_pos hcell hnext) hcell hσ x).trans
      (max_le (by rw [hleft]; exact mul_nonneg (by norm_num) (radialQ_nonneg N)) hright)

/-- A logarithmic cell comparison gives both multiplicative comparisons
with the same coefficient exponent. -/
theorem inner_ratios_le_coefficient_of_abs_log {u v b : ℝ} (hu : 0 < u) (hv : 0 < v)
    (m : ℕ) (h : |log (u / v)| ≤ b * radialQ m) :
    u / v ≤ radialE m ^ b ∧ v / u ≤ radialE m ^ b := by
  have he : exp (b * radialQ m) = radialE m ^ b := by
    rw [radialE, ← exp_mul]
    congr 1
    ring
  constructor
  · calc
      u / v = exp (log (u / v)) := (exp_log (div_pos hu hv)).symm
      _ ≤ exp (b * radialQ m) := exp_le_exp.mpr (abs_le.mp h).2
      _ = _ := he
  · calc
      v / u = exp (-log (u / v)) := by rw [exp_neg, exp_log (div_pos hu hv), inv_div]
      _ ≤ exp (b * radialQ m) := exp_le_exp.mpr (by linarith only [(abs_le.mp h).1])
      _ = _ := he

/-- The coefficient multiplier used in W₁ = W (E/E_N)^(-ℓ). -/
def innerCoefficientLoss (N : ℕ) (ℓ : ℝ) (m : ℕ) : ℝ :=
  (radialE m / radialE N) ^ (-ℓ)

theorem innerCoefficientLoss_eq_exp (N : ℕ) (ℓ : ℝ) (m : ℕ) :
    innerCoefficientLoss N ℓ m = exp (-(ℓ * (radialQ m - radialQ N))) := by
  rw [innerCoefficientLoss, radialE, radialE, ← exp_sub, ← exp_mul]
  congr 1
  ring

theorem innerCoefficientLoss_pos (N : ℕ) (ℓ : ℝ) (m : ℕ) :
    0 < innerCoefficientLoss N ℓ m := by
  rw [innerCoefficientLoss_eq_exp]
  exact exp_pos _

theorem innerCoefficientLoss_le_one {N m : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hm : N ≤ m) :
    innerCoefficientLoss N ℓ m ≤ 1 := by
  rw [innerCoefficientLoss_eq_exp, exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hℓ (sub_nonneg.mpr (radialQ_monotone hm)))

/-- The localized loss cancels a cell's coefficient power exactly. -/
theorem innerCoefficientLoss_cancel (N m : ℕ) (p : ℝ) :
    innerCoefficientLoss N p m * radialE m ^ p = radialE N ^ p := by
  rw [innerCoefficientLoss_eq_exp, radialE, radialE, ← exp_mul, ← exp_mul, ← exp_add]
  congr 1
  ring

theorem innerCoefficientLoss_absorb {N m : ℕ} {p ℓ : ℝ}
    (hm : N ≤ m) (hpℓ : p ≤ ℓ) :
    innerCoefficientLoss N ℓ m * radialE m ^ p ≤ radialE N ^ p := by
  have hmono : innerCoefficientLoss N ℓ m ≤ innerCoefficientLoss N p m := by
    rw [innerCoefficientLoss_eq_exp, innerCoefficientLoss_eq_exp]
    apply exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hpℓ
      (sub_nonneg.mpr (radialQ_monotone hm)))
  exact (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (exp_pos _).le _)).trans_eq
    (innerCoefficientLoss_cancel N m p)

/-- Every earlier coefficient is bounded by the transition-cell coefficient. -/
theorem inner_coefficient_power_le {m n : ℕ} (hmn : m ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    radialE m ^ p ≤ radialE n ^ p := by
  apply Real.rpow_le_rpow (exp_pos _).le _ hp
  exact exp_le_exp.mpr (radialQ_monotone hmn)

end ContinuousFlexibility.Radial
