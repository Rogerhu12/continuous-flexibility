module

public import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# The actual cell weights of the inner inverse

The coefficient and attenuation weights are the manuscript's actual
`radialE` and `radialH`. Their logarithmic adjacent ratio has a constant
independent of the base index and of the number of cells. Real powers
with absolute exponent at most one include both weighted estimates in
the inner inverse. The finite middle has the base weight, which is one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

/-- The cell weight in equation `rad-eq-hn4`. -/
def innerCellWeight (N : ℕ) (a γ : ℝ) (m : ℕ) : ℝ :=
  (radialE m / radialE N) ^ a * (radialH m / radialH N) ^ (-γ)

theorem innerCellWeight_pos (N : ℕ) (a γ : ℝ) (m : ℕ) :
    0 < innerCellWeight N a γ m :=
  mul_pos (rpow_pos_of_pos (div_pos (exp_pos _) (exp_pos _)) a)
    (rpow_pos_of_pos (div_pos (exp_pos _) (exp_pos _)) (-γ))

/-- The middle and the first retained cell have the same unit weight. -/
theorem innerCellWeight_base (N : ℕ) (a γ : ℝ) : innerCellWeight N a γ N = 1 := by
  rw [innerCellWeight, div_self (show radialE N ≠ 0 from exp_ne_zero _),
    div_self (show radialH N ≠ 0 from exp_ne_zero _), one_rpow, one_rpow, one_mul]

theorem innerCellWeight_log (N : ℕ) (a γ : ℝ) (m : ℕ) :
    log (innerCellWeight N a γ m) =
      a * (radialQ m - radialQ N) + γ * (radialS m - radialS N) := by
  have hE : 0 < radialE m / radialE N := div_pos (exp_pos _) (exp_pos _)
  have hH : 0 < radialH m / radialH N := div_pos (exp_pos _) (exp_pos _)
  rw [innerCellWeight, log_mul (rpow_pos_of_pos hE a).ne'
    (rpow_pos_of_pos hH (-γ)).ne', log_rpow hE, log_rpow hH,
    log_div (show radialE m ≠ 0 from exp_ne_zero _)
      (show radialE N ≠ 0 from exp_ne_zero _),
    log_div (show radialH m ≠ 0 from exp_ne_zero _)
      (show radialH N ≠ 0 from exp_ne_zero _)]
  simp only [radialE, radialH, log_exp]
  ring

/-- Taking a ratio cancels the base index exactly. -/
theorem innerCellWeight_log_ratio (N : ℕ) (a γ : ℝ) (k m : ℕ) :
    log (innerCellWeight N a γ k / innerCellWeight N a γ m) =
      a * (radialQ k - radialQ m) + γ * (radialS k - radialS m) := by
  rw [log_div (innerCellWeight_pos N a γ k).ne' (innerCellWeight_pos N a γ m).ne',
    innerCellWeight_log, innerCellWeight_log]
  ring

/-- One identity covers positive and negative weight powers. -/
theorem innerCellWeight_signed_log_ratio (N : ℕ) (a γ σ : ℝ) (k m : ℕ) :
    log ((innerCellWeight N a γ k) ^ σ / (innerCellWeight N a γ m) ^ σ) =
      σ * log (innerCellWeight N a γ k / innerCellWeight N a γ m) := by
  rw [log_div (rpow_pos_of_pos (innerCellWeight_pos N a γ k) σ).ne'
      (rpow_pos_of_pos (innerCellWeight_pos N a γ m) σ).ne',
    log_rpow (innerCellWeight_pos N a γ k),
    log_rpow (innerCellWeight_pos N a γ m),
    log_div (innerCellWeight_pos N a γ k).ne' (innerCellWeight_pos N a γ m).ne']
  ring

private theorem inner_weight_rpow_succ_le {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (3 / 2 : ℝ) ≤ 4 * x ^ (3 / 2 : ℝ) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  calc
    _ ≤ (2 * x) ^ (3 / 2 : ℝ) :=
      rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    _ = (2 : ℝ) ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) := mul_rpow (by norm_num) hx0
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (rpow_nonneg hx0 _)

private theorem inner_weight_log_succ_le {x : ℝ} (hx : 1 ≤ x) :
    log (exp 1 + x + 1) ≤ 2 * log (exp 1 + x) := by
  have he : 1 ≤ exp (1 : ℝ) := one_le_exp (by norm_num)
  have hy : 2 ≤ exp 1 + x := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hy) (by linarith : 0 ≤ exp 1 + x)
  have hsq : exp 1 + x + 1 ≤ (exp 1 + x) ^ 2 := by nlinarith only [hprod, hy]
  calc
    _ ≤ log ((exp 1 + x) ^ 2) := log_le_log (by linarith) hsq
    _ = _ := by rw [log_pow]; norm_num

/-- The coefficient increment in the precise unshifted form used in the
adjacent-weight estimate. -/
theorem inner_weight_radialQ_succ_sub_le {m : ℕ} (hm : 1 ≤ m) :
    radialQ (m + 1) - radialQ m ≤
      32 * (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow := inner_weight_rpow_succ_le hm1
  have hlog := inner_weight_log_succ_le hm1
  have hlog0 : 0 ≤ log (exp 1 + (m : ℝ) + 1) :=
    log_nonneg (by linarith [one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)])
  have hprod := mul_le_mul hpow hlog hlog0
    (by positivity : 0 ≤ 4 * (m : ℝ) ^ (3 / 2 : ℝ))
  have h := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 4)
  exact (radialQ_succ_sub_le m).trans (by nlinarith only [h])

theorem inner_weight_radialS_succ_sub_le {m : ℕ} (hm : 1 ≤ m) :
    radialS (m + 1) - radialS m ≤ 5 * (m : ℝ) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hquad := mul_nonneg (sub_nonneg.mpr hm1) (Nat.cast_nonneg (α := ℝ) m)
  rw [radialS_succ_sub_eq]
  nlinarith only [hm1, hquad]

/-- The paper's adjacent-weight estimate, with the explicit common
constant `32`, valid at every cell of index at least one. -/
theorem innerCellWeight_log_adjacent_le (N : ℕ) {a γ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    |log (innerCellWeight N a γ (m + 1) / innerCellWeight N a γ m)| ≤
      32 * (m : ℝ) ^ 2 + 32 * a * (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m) := by
  have hQ : 0 ≤ radialQ (m + 1) - radialQ m :=
    sub_nonneg.mpr (radialQ_monotone (Nat.le_succ m))
  have hS : 0 ≤ radialS (m + 1) - radialS m :=
    sub_nonneg.mpr (radialS_monotone (Nat.le_succ m))
  have hγS : |γ * (radialS (m + 1) - radialS m)| ≤ radialS (m + 1) - radialS m := by
    rw [abs_mul, abs_of_nonneg hS]
    exact mul_le_of_le_one_left hS hγ
  rw [innerCellWeight_log_ratio]
  calc
    _ ≤ |a * (radialQ (m + 1) - radialQ m)| +
        |γ * (radialS (m + 1) - radialS m)| := abs_add_le _ _
    _ ≤ a * (radialQ (m + 1) - radialQ m) + radialS (m + 1) - radialS m := by
      rw [abs_of_nonneg (mul_nonneg ha hQ)]
      linarith only [hγS]
    _ ≤ a * (32 * (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m)) + 5 * (m : ℝ) ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_left (inner_weight_radialQ_succ_sub_le hm) ha
      have h₂ := inner_weight_radialS_succ_sub_le hm
      linarith only [h₁, h₂]
    _ ≤ _ := by nlinarith only [sq_nonneg (m : ℝ)]

/-- Both signs use the same weight function and the same constant. The
slightly stronger range `|σ| ≤ 1` includes `σ = 1` and `σ = -1`. -/
theorem innerCellWeight_signed_log_adjacent_le (N : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    |log ((innerCellWeight N a γ (m + 1)) ^ σ / (innerCellWeight N a γ m) ^ σ)| ≤
      32 * (m : ℝ) ^ 2 + 32 * a * (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m) := by
  rw [innerCellWeight_signed_log_ratio, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hσ).trans
    (innerCellWeight_log_adjacent_le N ha hγ hm)

/-- A single constant works for every base index and every cell beyond
it; it does not depend on the eventual length of the finite inner chain. -/
theorem innerCellWeight_log_adjacent_uniform {a γ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ m : ℕ, N ≤ m →
      ∀ σ : ℝ, |σ| ≤ 1 →
        |log ((innerCellWeight N a γ (m + 1)) ^ σ / (innerCellWeight N a γ m) ^ σ)| ≤
          C * (m : ℝ) ^ 2 + C * a * (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m) := by
  refine ⟨32, by norm_num, ?_⟩
  intro N hN m hm σ hσ
  exact innerCellWeight_signed_log_adjacent_le N ha hγ hσ (hN.trans hm)

/-- In particular, the logarithmic variation costs only a fixed
coefficient power, uniformly for both signs. -/
theorem innerCellWeight_signed_log_coefficient_le (N : ℕ) {a γ σ : ℝ}
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    |log ((innerCellWeight N a γ (m + 1)) ^ σ / (innerCellWeight N a γ m) ^ σ)| ≤
      32 * (1 + a) * radialQ m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 ≤ log (exp 1 + (m : ℝ)) :=
    zero_le_one.trans (ssv_one_le_log (Nat.cast_nonneg m))
  have hp := mul_le_mul_of_nonneg_right
    (rpow_le_rpow_of_exponent_le hm1 (by norm_num : (3 / 2 : ℝ) ≤ 5 / 2)) hlog
  have hterm : (m : ℝ) ^ (3 / 2 : ℝ) * log (exp 1 + m) ≤ radialQ m := hp
  have hterm' := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 32 * a)
  have hsq := mul_le_mul_of_nonneg_left (radial_nat_sq_le_Q m) (by norm_num : (0 : ℝ) ≤ 32)
  exact (innerCellWeight_signed_log_adjacent_le N ha hγ hσ hm).trans
    (by nlinarith only [hterm', hsq])

/-- The gap weight is the geometric mean of its two neighboring cell
weights; assigning this one number at both endpoints preserves the gap. -/
def innerGeometricMeanWeight (u v : ℝ) : ℝ := sqrt (u * v)

theorem innerGeometricMeanWeight_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 < innerGeometricMeanWeight u v := sqrt_pos.mpr (mul_pos hu hv)

/-- Either endpoint has half the logarithmic adjacent variation. -/
theorem innerGeometricMeanWeight_log_ratio {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (right : Bool) :
    log (innerGeometricMeanWeight u v / (if right then v else u)) =
      (if right then -(1 / 2 : ℝ) else 1 / 2) * log (v / u) := by
  have hg := innerGeometricMeanWeight_pos hu hv
  have hlog : log (innerGeometricMeanWeight u v) = (log u + log v) / 2 := by
    rw [innerGeometricMeanWeight, log_sqrt (mul_nonneg hu.le hv.le), log_mul hu.ne' hv.ne']
  cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · rw [log_div hg.ne' hu.ne', hlog, log_div hv.ne' hu.ne']
    ring
  · rw [log_div hg.ne' hv.ne', hlog, log_div hv.ne' hu.ne']
    ring

end ContinuousFlexibility.Radial
