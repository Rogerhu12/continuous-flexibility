import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Analysis.MaterialWeights
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

/-!
# The scale budget of the accumulating Morse chain

The least nonsquare choices, the uniform height products in
`eq:rad-eq-js2`, and the absorption inequality in
`eq:rad-scale-separation` are the actual scalar quantities of Section 5.
They do not construct a Morse radius or identify the mass and resistance
intervals of a cell.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem positive_nat_nonsquare_or_succ {m : ℕ} (hm : 1 ≤ m) :
    (¬ ∃ k : ℕ, k ^ 2 = m) ∨ (¬ ∃ k : ℕ, k ^ 2 = m + 1) := by
  classical
  by_cases h : ∃ k : ℕ, k ^ 2 = m
  · right
    obtain ⟨k, hk⟩ := h
    rintro ⟨l, hl⟩
    have hkpos : 1 ≤ k := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hk0
      subst k
      norm_num at hk
      omega
    have hkl : k < l := by
      by_contra hkl
      have hlk : l ≤ k := by omega
      have hp := Nat.pow_le_pow_left hlk 2
      omega
    have hsucc : k + 1 ≤ l := by omega
    have hp := Nat.pow_le_pow_left hsucc 2
    nlinarith
  · exact Or.inl h

theorem exists_nonsquare_between (t : ℝ) (ht : 0 < t) :
    ∃ m : ℕ, t ≤ (m : ℝ) ∧ (m : ℝ) < t + 2 ∧ ¬ ∃ k : ℕ, k ^ 2 = m := by
  have hceilpos : 1 ≤ ⌈t⌉₊ := Nat.one_le_ceil_iff.mpr ht
  rcases positive_nat_nonsquare_or_succ hceilpos with h | h
  · refine ⟨⌈t⌉₊, Nat.le_ceil t, ?_, h⟩
    exact (Nat.ceil_lt_add_one ht.le).trans (by linarith)
  · refine ⟨⌈t⌉₊ + 1, ?_, ?_, h⟩
    · have hceil := Nat.le_ceil t
      push_cast
      linarith
    · have hceil := Nat.ceil_lt_add_one ht.le
      push_cast
      linarith

theorem exists_morseChainInteger (n : ℕ) :
    ∃ m : ℕ, exp ((n : ℝ) ^ 2) ≤ m ∧ ¬ ∃ k : ℕ, k ^ 2 = m := by
  obtain ⟨m, hm, _, hns⟩ := exists_nonsquare_between (exp ((n : ℝ) ^ 2)) (exp_pos _)
  exact ⟨m, hm, hns⟩

def morseChainInteger (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_morseChainInteger n)

theorem morseChainInteger_spec (n : ℕ) :
    exp ((n : ℝ) ^ 2) ≤ morseChainInteger n ∧
      ¬ ∃ k : ℕ, k ^ 2 = morseChainInteger n :=
  by
    classical
    exact Nat.find_spec (exists_morseChainInteger n)

theorem morseChainInteger_minimal (n k : ℕ)
    (hk : exp ((n : ℝ) ^ 2) ≤ k) (hkd : k < morseChainInteger n) :
    ∃ m : ℕ, m ^ 2 = k := by
  classical
  by_contra hns
  exact Nat.find_min (exists_morseChainInteger n) hkd ⟨hk, hns⟩

theorem morseChainInteger_lt (n : ℕ) :
    (morseChainInteger n : ℝ) < exp ((n : ℝ) ^ 2) + 2 := by
  classical
  obtain ⟨m, hm, hupper, hns⟩ :=
    exists_nonsquare_between (exp ((n : ℝ) ^ 2)) (exp_pos _)
  have hle : morseChainInteger n ≤ m := Nat.find_min' (exists_morseChainInteger n) ⟨hm, hns⟩
  exact (Nat.cast_le.mpr hle).trans_lt hupper

theorem morseChainInteger_ge_two (n : ℕ) : 2 ≤ morseChainInteger n := by
  have hs := morseChainInteger_spec n
  have he : (1 : ℝ) ≤ exp ((n : ℝ) ^ 2) := one_le_exp_iff.mpr (sq_nonneg _)
  have hdn : 1 ≤ morseChainInteger n := by exact_mod_cast he.trans hs.1
  have hne : morseChainInteger n ≠ 1 := by
    intro h
    exact hs.2 ⟨1, by simp only [h, one_pow]⟩
  omega

theorem morseChainInteger_error (n : ℕ) :
    |(morseChainInteger n : ℝ) - exp ((n : ℝ) ^ 2)| < 2 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (morseChainInteger_spec n).1)]
  linarith [morseChainInteger_lt n]

theorem finite_sigma_product_bounds {ι : Type*} (s : Finset ι) (σ : ι → ℝ)
    (hσ : ∀ i ∈ s, 1 ≤ σ i ∧ σ i ≤ 2) :
    1 ≤ (∏ i ∈ s, σ i) ∧ (∏ i ∈ s, σ i) ≤ (2 : ℝ) ^ s.card := by
  constructor
  · exact Finset.one_le_prod₀ (fun i hi => (hσ i hi).1)
  · simpa only [Finset.prod_const] using
      (Finset.prod_le_prod₀
        (fun i hi => zero_le_one.trans (hσ i hi).1)
        (fun i hi => (hσ i hi).2))

theorem morseChainAmplitude_bounds (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (n : ℕ) :
    exp (-(n : ℝ) ^ (5 / 2 : ℝ)) ≤ Statements.morseChainAmplitude T σ n ∧
      Statements.morseChainAmplitude T σ n ≤
        exp (-(n : ℝ) ^ (5 / 2 : ℝ)) * (2 : ℝ) ^ (Finset.Icc T.index n).card := by
  have hprod := finite_sigma_product_bounds (Finset.Icc T.index n) σ (fun i _ => hσ i)
  constructor
  · simpa only [Statements.morseChainAmplitude, mul_one] using
      mul_le_mul_of_nonneg_left hprod.1 (exp_pos (-(n : ℝ) ^ (5 / 2 : ℝ))).le
  · exact mul_le_mul_of_nonneg_left hprod.2 (exp_pos _).le

theorem morseChainAmplitude_pos (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (n : ℕ) :
    0 < Statements.morseChainAmplitude T σ n :=
  (exp_pos _).trans_le (morseChainAmplitude_bounds T σ hσ n).1

theorem morseChainAmplitude_log_bounds (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (n : ℕ) :
    -(n : ℝ) ^ (5 / 2 : ℝ) ≤ log (Statements.morseChainAmplitude T σ n) ∧
    log (Statements.morseChainAmplitude T σ n) ≤
      -(n : ℝ) ^ (5 / 2 : ℝ) + ((n : ℝ) + 1) * log 2 := by
  let x : ℝ := -(n : ℝ) ^ (5 / 2 : ℝ)
  let m : ℕ := (Finset.Icc T.index n).card
  have hb : exp x ≤ Statements.morseChainAmplitude T σ n ∧
      Statements.morseChainAmplitude T σ n ≤ exp x * (2 : ℝ) ^ m :=
    morseChainAmplitude_bounds T σ hσ n
  refine ⟨?_, ?_⟩
  · simpa only [log_exp] using Real.log_le_log (exp_pos x) hb.1
  · have hu := Real.log_le_log (morseChainAmplitude_pos T σ hσ n) hb.2
    rw [Real.log_mul (Real.exp_ne_zero x) (pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0)),
      Real.log_exp, Real.log_pow] at hu
    have hmN : m ≤ n + 1 := by
      dsimp only [m]
      rw [Nat.card_Icc]
      exact Nat.sub_le _ _
    have hm : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hmN
    exact hu.trans (add_le_add_right
      (mul_le_mul_of_nonneg_right hm (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) x)

theorem morseChainAmplitude_succ (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (n : ℕ) (hn : T.index ≤ n + 1) :
    Statements.morseChainAmplitude T σ (n + 1) =
      σ (n + 1) * exp ((n : ℝ) ^ (5 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ)) *
        Statements.morseChainAmplitude T σ n := by
  have hset : Finset.Icc T.index (n + 1) = insert (n + 1) (Finset.Icc T.index n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : n + 1 ∉ Finset.Icc T.index n := by
    simp only [Finset.mem_Icc]
    omega
  let a : ℝ := (n : ℝ) ^ (5 / 2 : ℝ)
  let b : ℝ := ((n + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ)
  have he : exp (a - b) * exp (-a) = exp (-b) := by
    rw [← exp_add]
    congr 1
    ring
  unfold Statements.morseChainAmplitude
  rw [hset, Finset.prod_insert hnotmem]
  change exp (-b) * (σ (n + 1) * ∏ k ∈ Finset.Icc T.index n, σ k) =
    σ (n + 1) * exp (a - b) * (exp (-a) * ∏ k ∈ Finset.Icc T.index n, σ k)
  rw [show σ (n + 1) * exp (a - b) *
      (exp (-a) * ∏ k ∈ Finset.Icc T.index n, σ k) =
      (σ (n + 1) * (exp (a - b) * exp (-a))) * ∏ k ∈ Finset.Icc T.index n, σ k by ring,
    he]
  ring

theorem radial_nat_sq_le_Q (n : ℕ) : (n : ℝ) ^ 2 ≤ Statements.radialQ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [Statements.radialQ]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hp : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by
      calc
        _ = (n : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast (n : ℝ) 2).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have hl : 1 ≤ Real.log (Real.exp 1 + (n : ℝ)) := by
      calc
        1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right (Nat.cast_nonneg n))
    exact hp.trans (by
      simpa only [Statements.radialQ, mul_one] using
        mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg (Nat.cast_nonneg n) (5 / 2 : ℝ)))

theorem radial_scale_absorption (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      Statements.radialE n ^ a * Real.exp (b * (n : ℝ) ^ 2) ≤
        K * Real.exp (ε * Statements.radialS n) := by
  let A : ℝ := |a| + |b|
  have hA : 0 ≤ A := add_nonneg (abs_nonneg a) (abs_nonneg b)
  obtain ⟨K, hK, hAbs⟩ := Analysis.materialH_rpow_mul_materialE0_rpow_le A hε
  refine ⟨K, hK, ?_⟩
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq := radial_nat_sq_le_Q n
  have hQ : 0 ≤ Statements.radialQ n := (sq_nonneg (n : ℝ)).trans hsq
  have he : a * Statements.radialQ n + b * (n : ℝ) ^ 2 ≤
      A * (1 + Statements.radialQ n) := by
    calc
      _ ≤ |a| * Statements.radialQ n + |b| * Statements.radialQ n :=
        add_le_add (mul_le_mul_of_nonneg_right (le_abs_self a) hQ)
          ((mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg (n : ℝ))).trans
            (mul_le_mul_of_nonneg_left hsq (abs_nonneg b)))
      _ = A * Statements.radialQ n := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hA
  have hDom : Statements.radialE n ^ a * Real.exp (b * (n : ℝ) ^ 2) ≤
      Analysis.materialE0 (n : ℝ) ^ A := by
    calc
      _ = Real.exp (a * Statements.radialQ n + b * (n : ℝ) ^ 2) := by
        rw [Statements.radialE, ← Real.exp_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (A * (1 + Statements.radialQ n)) := Real.exp_le_exp.mpr he
      _ = _ := by
        change Real.exp (A * (1 + Statements.radialQ n)) = Real.exp (1 + Statements.radialQ n) ^ A
        rw [← Real.exp_mul]
        congr 1
        ring
  have hH : Analysis.materialH (n : ℝ) ^ ε = Real.exp (-(ε * Statements.radialS n)) := by
    rw [Analysis.materialH, ← Real.exp_mul]
    congr 1
    unfold Statements.radialS
    ring
  have hb := (mul_le_mul_of_nonneg_left hDom
    (Real.rpow_nonneg (Analysis.materialH_pos (n : ℝ)).le ε)).trans (hAbs (n : ℝ) hn0)
  rw [hH] at hb
  calc
    _ = Real.exp (ε * Statements.radialS n) *
        (Real.exp (-(ε * Statements.radialS n)) *
          (Statements.radialE n ^ a * Real.exp (b * (n : ℝ) ^ 2))) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (ε * Statements.radialS n) * K :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end ContinuousFlexibility.Radial
