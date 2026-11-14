module

public import ContinuousFlexibility.Radial.WeightKernelBounds
public import Mathlib.Tactic.NormNum

/-!
# Fixed-index-window weight comparisons

On a fixed finite index window, both attenuation and coefficient
exponents vary by at most a fixed multiple of `1 + radialQ n`. Thus a
fixed coefficient loss in an endpoint-layer energy estimate is absorbed
by enlarging the output exponent, uniformly for `|γ| ≤ 1`.
-/

@[expose] public section

open Real
open ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Radial

noncomputable section

theorem radialS_sub_le_Q_of_index_window (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n k : ℕ, n ≤ k + N → k ≤ n + N →
      |radialS k - radialS n| ≤ A * (1 + radialQ n) := by
  let R : ℝ := N
  let A : ℝ := 4 * R * (1 + R ^ 2) + 1
  have hR : 0 ≤ R := Nat.cast_nonneg N
  have hA : 1 ≤ A := by
    have hh : 0 ≤ 4 * R * (1 + R ^ 2) := by positivity
    dsimp only [A]
    linarith only [hh]
  refine ⟨A, hA, ?_⟩
  intro n k hnk hkn
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnk' : (n : ℝ) ≤ (k : ℝ) + R := by
    change (n : ℝ) ≤ (k : ℝ) + (N : ℝ)
    exact_mod_cast hnk
  have hkn' : (k : ℝ) ≤ (n : ℝ) + R := by
    change (k : ℝ) ≤ (n : ℝ) + (N : ℝ)
    exact_mod_cast hkn
  have hgap : |(k : ℝ) - n| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn' : (n : ℝ) ≤ (n : ℝ) + R := le_add_of_nonneg_right hR
  have hkk := pow_le_pow_left₀ hk hkn' 2
  have hnn := pow_le_pow_left₀ hn hn' 2
  have hkn₂ := mul_le_mul hkn' hn' hn (add_nonneg hn hR)
  have hP : (k : ℝ) ^ 2 + (k : ℝ) * n + (n : ℝ) ^ 2 ≤
      3 * ((n : ℝ) + R) ^ 2 := by nlinarith only [hkk, hnn, hkn₂]
  have hP₀ : 0 ≤ (k : ℝ) ^ 2 + (k : ℝ) * n + (n : ℝ) ^ 2 := by positivity
  have hprod := mul_le_mul hgap hP hP₀ hR
  have he : radialS k - radialS n =
      (2 / 3 : ℝ) * ((k : ℝ) - n) *
        ((k : ℝ) ^ 2 + (k : ℝ) * n + (n : ℝ) ^ 2) := by
    unfold radialS
    ring
  have hraw : |radialS k - radialS n| ≤ 2 * R * ((n : ℝ) + R) ^ 2 := by
    rw [he, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3),
      abs_of_nonneg hP₀]
    nlinarith only [hprod]
  have hsq : ((n : ℝ) + R) ^ 2 ≤ 2 * ((n : ℝ) ^ 2 + R ^ 2) := by
    nlinarith only [sq_nonneg ((n : ℝ) - R)]
  have hscaled := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * R)
  have hQ := radial_nat_sq_le_Q n
  have hQ₀ := radialQ_nonneg n
  have hQscaled := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 4 * R)
  calc
    |radialS k - radialS n| ≤ 4 * R * (radialQ n + R ^ 2) := by
      nlinarith only [hraw, hscaled, hQscaled]
    _ ≤ 4 * R * ((1 + R ^ 2) * (1 + radialQ n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [mul_nonneg (sq_nonneg R) hQ₀]
    _ = (A - 1) * (1 + radialQ n) := by dsimp [A]; ring
    _ ≤ A * (1 + radialQ n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem radialSQ_sub_le_Q_of_index_window (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n k : ℕ, n ≤ k + N → k ≤ n + N →
      |radialS k - radialS n| ≤ A * (1 + radialQ n) ∧
        |radialQ k - radialQ n| ≤ A * (1 + radialQ n) := by
  obtain ⟨A₀, hA₀, hS⟩ := radialS_sub_le_Q_of_index_window N
  obtain ⟨C, hC⟩ := radialQ_sub_le 1 (by norm_num)
  let A : ℝ := A₀ + |C| + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg C]
  refine ⟨A, hA, ?_⟩
  intro n k hnk hkn
  have hQ₀ := radialQ_nonneg n
  have hS' := hS n k hnk hkn
  have hcoef : A₀ * (1 + radialQ n) ≤ A * (1 + radialQ n) :=
    mul_le_mul_of_nonneg_right (by dsimp [A]; linarith [abs_nonneg C]) (by positivity)
  refine ⟨hS'.trans hcoef, ?_⟩
  have hC' := hC k n
  have hnonneg := mul_nonneg (show 0 ≤ |C| + 1 by positivity) hQ₀
  dsimp only [A]
  nlinarith only [hC', hS', hnonneg, le_abs_self C]

/-- One output-exponent loss absorbs any fixed coefficient power on a
finite index window, simultaneously for every attenuation exponent in
`[-1,1]`. -/
theorem output_weight_absorb_on_index_window (N : ℕ) (D M : ℝ) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 < K ∧
      ∀ γ : ℝ, |γ| ≤ 1 → ∀ n k : ℕ, n ≤ k + N → k ≤ n + N →
        exp (D * radialQ n) * exp (-2 * (M + L) * radialQ n + 2 * γ * radialS n) ≤
          K * exp (-2 * M * radialQ k + 2 * γ * radialS k) := by
  obtain ⟨A, hA, hAQ⟩ := radialSQ_sub_le_Q_of_index_window N
  let P : ℝ := 2 * (|M| + 1) * A
  let L : ℝ := |D| + P + 1
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨L, exp P, hL, exp_pos _, ?_⟩
  intro γ hγ n k hnk hkn
  obtain ⟨hS, hQ⟩ := hAQ n k hnk hkn
  have hQ₀ := radialQ_nonneg n
  have hMdiff : 2 * M * (radialQ k - radialQ n) ≤
      2 * |M| * (A * (1 + radialQ n)) := by
    have h₀ : M * (radialQ k - radialQ n) ≤ |M| * |radialQ k - radialQ n| := by
      calc
        _ ≤ |M * (radialQ k - radialQ n)| := le_abs_self _
        _ = _ := abs_mul _ _
    have h₁ := mul_le_mul_of_nonneg_left hQ (abs_nonneg M)
    nlinarith only [h₀, h₁]
  have hγdiff : 2 * γ * (radialS n - radialS k) ≤
      2 * (A * (1 + radialQ n)) := by
    have h₀ : γ * (radialS n - radialS k) ≤ |γ| * |radialS k - radialS n| := by
      calc
        _ ≤ |γ * (radialS n - radialS k)| := le_abs_self _
        _ = |γ| * |radialS n - radialS k| := abs_mul _ _
        _ = _ := by rw [abs_sub_comm (radialS n)]
    have h₁ := mul_le_mul hγ hS (abs_nonneg _) zero_le_one
    nlinarith only [h₀, h₁]
  have hD := mul_le_mul_of_nonneg_right (le_abs_self D) hQ₀
  have hnonneg := mul_nonneg (show 0 ≤ |D| + P + 2 by positivity) hQ₀
  have hexp : D * radialQ n + (-2 * (M + L) * radialQ n + 2 * γ * radialS n) ≤
      P + (-2 * M * radialQ k + 2 * γ * radialS k) := by
    dsimp only [P, L] at *
    nlinarith only [hMdiff, hγdiff, hD, hnonneg]
  rw [← exp_add, ← exp_add]
  exact exp_le_exp.mpr hexp

end

end ContinuousFlexibility.Radial
