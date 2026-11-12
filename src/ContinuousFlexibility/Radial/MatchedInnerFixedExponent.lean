import ContinuousFlexibility.Radial.InnerCoefficientCosts

/-!
# A fixed coarse exponent for every later actual inner inverse

The constants in the local Dirichlet and Poisson estimates are fixed
before the first index is selected. Increasing that index absorbs those
constants into one additional coefficient power, uniformly over every
later cell and every frequency at least one. The retained length is not
used in the choice.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

theorem inner_radialQ_ge_index {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ radialQ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hnR (by norm_num)
  exact hp.trans (le_mul_of_one_le_right
    (rpow_nonneg (Nat.cast_nonneg n) _) (ssv_one_le_log (Nat.cast_nonneg n)))

/-- One coefficient power absorbs the fixed local constants once the
actual coefficient exceeds their sum. -/
theorem inner_coefficient_absorb_cost_at_threshold {K C p : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hp : 0 ≤ p) (hsize : K + C ≤ radialE n) :
    K * radialE n ^ p + C ≤ radialE n ^ (p + 1) := by
  have hE : 0 < radialE n := exp_pos _
  have hEp : 1 ≤ radialE n ^ p := by
    rw [radialE, ← exp_mul, one_le_exp_iff]
    exact mul_nonneg (radialQ_nonneg n) hp
  calc
    K * radialE n ^ p + C ≤ K * radialE n ^ p + C * radialE n ^ p :=
      add_le_add le_rfl (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hEp hC)
    _ = (K + C) * radialE n ^ p := by ring
    _ ≤ radialE n * radialE n ^ p :=
      mul_le_mul_of_nonneg_right hsize (rpow_pos_of_pos hE p).le
    _ = radialE n ^ (p + 1) := by
      rw [rpow_add hE, rpow_one]
      ring

/-- The original later-cell exponent 38 is uniform in the retained
length and frequency. The same choice also meets the genuine Morse
weight threshold for any previously fixed weight exponent. -/
theorem exists_innerActualInverse_fixed_exponent
    (K CP a : ℝ) (initial : ℕ) :
    ∃ N : ℕ, initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
      ∀ n : ℕ, N ≤ n → ∀ j : ℝ, 1 ≤ j →
        K * radialE n ^ (37 : ℝ) + 2 * CP ^ 2 / j ^ 2 ≤
          radialE n ^ (38 : ℝ) := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (K + 2 * CP ^ 2)
  obtain ⟨N, hN, hlarge, ha⟩ :=
    exists_innerCellWeight_fixed_exponent a (max initial J)
  refine ⟨N, (le_max_left _ _).trans hN, hlarge, ha, ?_⟩
  intro n hn j hj
  have hJn : J ≤ n := ((le_max_right _ _).trans hN).trans hn
  have hn1 : 1 ≤ n := by omega
  have hsize : K + 2 * CP ^ 2 ≤ radialE n := by
    have hcast : (J : ℝ) ≤ n := by exact_mod_cast hJn
    have hq := inner_radialQ_ge_index hn1
    have hexp := add_one_le_exp (radialQ n)
    change K + 2 * CP ^ 2 ≤ exp (radialQ n)
    linarith only [hJ, hcast, hq, hexp]
  have hc : 2 * CP ^ 2 / j ^ 2 ≤ 2 * CP ^ 2 :=
    div_le_self (by positivity) (one_le_pow₀ hj)
  exact (add_le_add le_rfl hc).trans (by
    simpa only [show (37 : ℝ) + 1 = 38 by norm_num] using
      inner_coefficient_absorb_cost_at_threshold
        (K := K) (C := 2 * CP ^ 2) (p := 37) (by positivity) (by norm_num) hsize)

/-- The Hardy gap contribution also has a fixed exponent. Its endpoint
cost and the actual model-column constant are chosen before the first
index, and the resulting threshold is uniform over all later modes. -/
theorem exists_innerActualHardyInverse_fixed_exponent
    (K KP CE a : ℝ) (hCE : 0 ≤ CE) (initial : ℕ) :
    ∃ N : ℕ, initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
      ∀ n : ℕ, N ≤ n → ∀ j : ℝ, 1 ≤ j →
        K * radialE n ^ (37 : ℝ) +
          2 * (max ((2 * KP / j) ^ 2) 48 + 24 * CE) ≤ radialE n ^ (38 : ℝ) := by
  let cost : ℝ := max ((2 * KP) ^ 2) 48 + 24 * CE
  have hcost : 0 ≤ cost := add_nonneg
    ((sq_nonneg _).trans (le_max_left _ _)) (mul_nonneg (by norm_num) hCE)
  obtain ⟨N, hN, hlarge, ha, hbound⟩ :=
    exists_innerActualInverse_fixed_exponent K (sqrt cost) a initial
  refine ⟨N, hN, hlarge, ha, ?_⟩
  intro n hn j hj
  have hquot : (2 * KP / j) ^ 2 ≤ (2 * KP) ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg _) (one_le_pow₀ hj)
  have hcor : max ((2 * KP / j) ^ 2) 48 + 24 * CE ≤ cost :=
    add_le_add (max_le_max hquot le_rfl) le_rfl
  have hconst := hbound n hn 1 le_rfl
  rw [sq_sqrt hcost] at hconst
  simp only [one_pow, div_one] at hconst
  exact (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hcor (by norm_num : (0 : ℝ) ≤ 2))).trans hconst

end ContinuousFlexibility.Radial
