import ContinuousFlexibility.Analysis.N01aOpticalNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Coefficient powers for the optical construction

These are numerical consequences of the single hypothesis `1 ≤ E`.
The same actual radicand and control are used throughout; finite jet
bounds merely enlarge the coefficient and exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

theorem n01aOptical_power_mono {E A B : ℝ} (hE : 1 ≤ E) (hA : 0 ≤ A) (hAB : A ≤ B) :
    A * E ^ A ≤ B * E ^ B :=
  mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) (hA.trans hAB)

theorem n01aOptical_absorb_power (a b : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : ℝ, 1 ≤ E → a * E ^ b ≤ C * E ^ C := by
  let C : ℝ := 1 + |a| + |b|
  have hC : 0 < C := by dsimp [C]; positivity
  have haC : a ≤ C := by dsimp [C]; linarith [le_abs_self a, abs_nonneg b]
  have hbC : b ≤ C := by dsimp [C]; linarith [le_abs_self b, abs_nonneg a]
  refine ⟨C, hC, fun E hE => ?_⟩
  exact mul_le_mul haC (Real.rpow_le_rpow_of_exponent_le hE hbC)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) hC.le

theorem n01aOptical_power_product_bound {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : ℝ, 1 ≤ E →
      (A * E ^ A) * (B * E ^ B) ≤ C * E ^ C := by
  obtain ⟨C, hC, hc⟩ := n01aOptical_absorb_power (A * B) (A + B) (mul_nonneg hA.le hB.le)
  refine ⟨C, hC, fun E hE => ?_⟩
  have heq : (A * E ^ A) * (B * E ^ B) = (A * B) * E ^ (A + B) := by
    rw [Real.rpow_add (zero_lt_one.trans_le hE)]
    ring
  rw [heq]
  exact hc E hE

/-- Finitely many given derivative bounds admit one common coefficient. -/
theorem n01aOptical_finite_weightedJet_bound {ι : Type*} {E l h : ι → ℝ} {q : ℝ → ℝ}
    (hE : ∀ i, 1 ≤ E i)
    (hjets : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i r, r ∈ Icc (l i) (h i) →
      |iteratedDeriv s q r| ≤ C * E i ^ C) (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k ≤ s, ∀ i r, r ∈ Icc (l i) (h i) →
      |iteratedDeriv k q r| ≤ C * E i ^ C := by
  induction s with
  | zero =>
      obtain ⟨A, hA, ha⟩ := hjets 0
      refine ⟨A + 1, by linarith, fun k hk i r hr => ?_⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact (ha i r hr).trans (n01aOptical_power_mono (hE i) hA.le (by linarith))
  | succ s ih =>
      obtain ⟨A, hA, ha⟩ := ih
      obtain ⟨B, hB, hb⟩ := hjets (s + 1)
      let C : ℝ := A + B + 1
      have hC : 1 ≤ C := by dsimp [C]; linarith
      have hAC : A ≤ C := by dsimp [C]; linarith
      have hBC : B ≤ C := by dsimp [C]; linarith
      refine ⟨C, hC, fun k hk i r hr => ?_⟩
      by_cases hks : k ≤ s
      · exact (ha k hks i r hr).trans
          (n01aOptical_power_mono (hE i) (zero_le_one.trans hA) hAC)
      · have heq : k = s + 1 := by omega
        subst k
        exact (hb i r hr).trans (n01aOptical_power_mono (hE i) hB.le hBC)

def n01aOpticalScale (E A L : ℝ) : ℝ := (E ^ (-A) / (4 * L)) ^ 2

theorem n01aOpticalScale_pos {E A L : ℝ} (hE : 0 < E) (hL : 0 < L) :
    0 < n01aOpticalScale E A L :=
  sq_pos_of_pos (div_pos (Real.rpow_pos_of_pos hE _) (mul_pos (by norm_num) hL))

theorem n01aOpticalScale_sqrt {E A L : ℝ} (hE : 0 < E) (hL : 0 < L) :
    4 * L * Real.sqrt (n01aOpticalScale E A L) = E ^ (-A) := by
  rw [n01aOpticalScale, Real.sqrt_sq
    (div_nonneg (Real.rpow_nonneg hE.le _) (mul_nonneg (by norm_num) hL.le))]
  field_simp [hL.ne']

theorem n01aOpticalScale_inv {E A L : ℝ} (hE : 0 < E) :
    (n01aOpticalScale E A L)⁻¹ = (4 * L) ^ 2 * E ^ (2 * A) := by
  rw [n01aOpticalScale, div_pow, inv_div, Real.rpow_neg hE.le,
    inv_pow, div_inv_eq_mul]
  congr 1
  simpa only [Nat.cast_ofNat, mul_comm] using (Real.rpow_mul_natCast hE.le A 2).symm

theorem n01aOptical_quadratic_scale_bound {β A B : ℝ}
    (hβ : 0 ≤ β) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ E δ : ℝ, 1 ≤ E → 0 < δ → δ⁻¹ ≤ B * E ^ B →
      β * (A * E ^ A) ^ 2 / δ ≤ C * E ^ C := by
  obtain ⟨C, hC, hc⟩ := n01aOptical_absorb_power (β * A ^ 2 * B) (2 * A + B)
    (mul_nonneg (mul_nonneg hβ (sq_nonneg A)) hB.le)
  refine ⟨C, hC, fun E δ hE hδ hinv => ?_⟩
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have htwice : E ^ (2 * A) = (E ^ A) ^ 2 := by
    simpa only [Nat.cast_ofNat, mul_comm] using Real.rpow_mul_natCast hEpos.le A 2
  have hproduct : β * (A * E ^ A) ^ 2 * (B * E ^ B) =
      (β * A ^ 2 * B) * E ^ (2 * A + B) := by
    rw [mul_pow, Real.rpow_add hEpos, htwice]
    ring
  calc
    β * (A * E ^ A) ^ 2 / δ = β * (A * E ^ A) ^ 2 * δ⁻¹ := div_eq_mul_inv _ _
    _ ≤ β * (A * E ^ A) ^ 2 * (B * E ^ B) :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg hβ (sq_nonneg _))
    _ = (β * A ^ 2 * B) * E ^ (2 * A + B) := hproduct
    _ ≤ C * E ^ C := hc E hE

theorem n01aOptical_polynomial_scale_bound (s : ℕ) {F β A B : ℝ}
    (hF : 0 < F) (hβ : 0 ≤ β) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ E δ : ℝ, 1 ≤ E → 0 < δ → δ⁻¹ ≤ B * E ^ B →
      F * (1 + β) * (1 + (A * E ^ A) / δ) ^ s ≤ C * E ^ C := by
  let a : ℝ := F * (1 + β) * (1 + A * B) ^ s
  let b : ℝ := (A + B) * (s : ℝ)
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg hF.le (by linarith))
    (pow_nonneg (by positivity) _)
  obtain ⟨C, hC, hc⟩ := n01aOptical_absorb_power a b ha
  refine ⟨C, hC, fun E δ hE hδ hinv => ?_⟩
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hAE : 0 ≤ A * E ^ A := mul_nonneg hA.le (Real.rpow_nonneg hEpos.le _)
  have hproduct : (A * E ^ A) / δ ≤ (A * B) * E ^ (A + B) := by
    calc
      (A * E ^ A) / δ = (A * E ^ A) * δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ (A * E ^ A) * (B * E ^ B) := mul_le_mul_of_nonneg_left hinv hAE
      _ = (A * B) * E ^ (A + B) := by rw [Real.rpow_add hEpos]; ring
  have hone : 1 ≤ E ^ (A + B) := Real.one_le_rpow hE (add_nonneg hA.le hB.le)
  have hplus : 1 + (A * E ^ A) / δ ≤ (1 + A * B) * E ^ (A + B) := by
    calc
      1 + (A * E ^ A) / δ ≤ 1 + (A * B) * E ^ (A + B) := add_le_add le_rfl hproduct
      _ ≤ E ^ (A + B) + (A * B) * E ^ (A + B) := add_le_add hone le_rfl
      _ = (1 + A * B) * E ^ (A + B) := by ring
  have hbase : 0 ≤ 1 + (A * E ^ A) / δ := by positivity
  have hp := pow_le_pow_left₀ hbase hplus s
  rw [mul_pow, ← Real.rpow_mul_natCast hEpos.le (A + B) s] at hp
  have hmajor := mul_le_mul_of_nonneg_left hp (mul_nonneg hF.le (by linarith : 0 ≤ 1 + β))
  have heq : F * (1 + β) * ((1 + A * B) ^ s * E ^ ((A + B) * (s : ℝ))) =
      a * E ^ b := by dsimp [a, b]; ring
  exact (hmajor.trans_eq heq).trans (hc E hE)

end ContinuousFlexibility.Statements
