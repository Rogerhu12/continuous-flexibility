import ContinuousFlexibility.Radial.R07DeepTailHypotheses

/-!
# The physical flatness product bound

The leading coefficient `2` in the quadratic exponent is preserved.
All fixed normalization losses are absorbed by a multiple of `n^(3/2)+n`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

theorem r07_deepTail_lambda_one_le {T : MorseChainData} {D : ReferenceData} {right : Bool}
    {j start : ℕ} {η K : ℝ} (hj : 2 ≤ j) :
    1 ≤ (r07DeepTailData T D right j start η K).Λ := by
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj2 : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by
    nlinarith only [hj', sq_nonneg ((j : ℝ) - 2)]
  change 1 ≤ (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)
  nlinarith only [hj2, mul_nonneg (sub_nonneg.mpr hj2) (sq_nonneg (j : ℝ))]

theorem r07_absorb_sharp_constant {C Λ : ℝ} (hC : 0 < C) (hΛ : 1 ≤ Λ)
    {n : ℕ} (hn : 1 ≤ n) :
    exp (2 * (n : ℝ) ^ 2 - (100 + 2 * |log C|) * ((n : ℝ) ^ (3 / 2 : ℝ) + n)) ≤
      (exp (-2) * Λ / C ^ 2) *
        exp (2 * (n : ℝ) ^ 2 - 10 * (n : ℝ) ^ (3 / 2 : ℝ) - 4 * n - 51) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := rpow_nonneg (Nat.cast_nonneg n) _
  have hcoeff : 0 < exp (-2) * Λ / C ^ 2 := by positivity
  apply (le_log_iff_exp_le (mul_pos hcoeff (exp_pos _))).mp
  rw [log_mul hcoeff.ne' (exp_ne_zero _),
    log_div (mul_ne_zero (exp_ne_zero _) hΛp.ne') (pow_ne_zero 2 hC.ne'),
    log_mul (exp_ne_zero _) hΛp.ne', log_pow]
  simp only [log_exp, Nat.cast_ofNat]
  have hmulP : 10 * (n : ℝ) ^ (3 / 2 : ℝ) ≤
      (100 + 2 * |log C|) * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (by nlinarith only [abs_nonneg (log C)]) hp
  have hmulN : 4 * (n : ℝ) + 53 + 2 * |log C| ≤ (100 + 2 * |log C|) * n := by
    nlinarith only [hn', mul_nonneg (abs_nonneg (log C)) (sub_nonneg.mpr hn')]
  nlinarith only [hmulP, hmulN, log_nonneg hΛ, le_abs_self (log C)]

theorem r07_deepTail_physical_product {T : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds T σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : T.index < start) (h32 : 32 ≤ start) (η K : ℝ)
    (hclose : (r07DeepTailData T D right j start η K).endpoint -
      (r07DeepTailData T D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    let Q := r07DeepTailData T D right j start η K
    ∃ L : ℝ, 0 < L ∧ ∀ n,
      exp (2 * ((start + n : ℕ) : ℝ) ^ 2 -
        L * (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) ≤
          Q.Λ * tailMass Q (n + 1) * tailResistance Q n := by
  refine ⟨100 + 2 * |log (C 0)|, by positivity, ?_⟩
  intro n
  have hbnd := (r07_deepTail_adjacent_products h hσ hb right hj hstart h32 η K hclose
    n (n + 1) (Or.inr rfl)).2.2
  exact (r07_absorb_sharp_constant (h.constants_pos 0)
    (r07_deepTail_lambda_one_le hj) (by omega : 1 ≤ start + n)).trans hbnd

end ContinuousFlexibility.Radial
