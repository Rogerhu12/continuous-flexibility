module

public import ContinuousFlexibility.Analysis.N04NegativeInverseJetEnvelope

/-!
# Finite composition coefficients in one material envelope

Every constant in this module is chosen before the material sample and
before the derivative order inside the requested finite prefix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem n04NegativeInverse_envelope_mono {B D E : ℝ}
    (hD : 0 ≤ D) (hBD : B ≤ D) (hE : 1 ≤ E) :
    B * E ^ B ≤ D * E ^ D :=
  mul_le_mul hBD (Real.rpow_le_rpow_of_exponent_le hE hBD)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) hD

theorem n04NegativeInverse_envelope_one_le {B E : ℝ}
    (hB : 1 ≤ B) (hE : 1 ≤ E) : 1 ≤ B * E ^ B :=
  one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hE (zero_le_one.trans hB))

/-- The scalar root transition has a bounded outer derivative, a
finite partition count and one source bound for each block. All of
these costs share a single sample-independent material envelope. -/
theorem n04NegativeInverse_finiteComposition_envelope
    (N : ℕ) {C L D : ℝ} (hC : 1 ≤ C) (hL : 1 ≤ L) (hD : 1 ≤ D) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ E : ℝ, 1 ≤ E →
      D * E ^ D ≤ B * E ^ B ∧
      ∀ n : ℕ, n ≤ N →
        ((2 : ℝ) ^ N * C * (1 + D * E ^ D)) *
          (Fintype.card (OrderedFinpartition n) : ℝ) *
            ((D * E ^ D) * L) ^ n ≤ B * E ^ B := by
  classical
  let P : ℝ := ∑ i : Fin (N + 1), (Fintype.card (OrderedFinpartition i.val) : ℝ)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let A : ℝ := (2 : ℝ) ^ N * C * (1 + D) * P * (D * L) ^ N
  let d : ℝ := D + D * (N : ℝ)
  obtain ⟨B₀, hB₀, hpack⟩ := coefficientEnvelope_pack A d
  let B : ℝ := max 1 (max D B₀)
  have hB : 1 ≤ B := le_max_left _ _
  have hDB : D ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB₀B : B₀ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro E hE
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hED : 1 ≤ E ^ D := Real.one_le_rpow hE hD0
  have hQ : 1 ≤ (D * E ^ D) * L :=
    one_le_mul_of_one_le_of_one_le
      (n04NegativeInverse_envelope_one_le hD hE) hL
  refine ⟨n04NegativeInverse_envelope_mono (zero_le_one.trans hB) hDB hE, ?_⟩
  intro n hn
  have hnP : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ P :=
    Finset.single_le_sum (fun i _ => Nat.cast_nonneg
      (Fintype.card (OrderedFinpartition i.val)))
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (N + 1)))
  have houter : 1 + D * E ^ D ≤ (1 + D) * E ^ D := by
    nlinarith only [hED]
  have hcoef : ((2 : ℝ) ^ N * C * (1 + D * E ^ D)) *
        (Fintype.card (OrderedFinpartition n) : ℝ) *
          ((D * E ^ D) * L) ^ n ≤ A * E ^ d := by
    calc
      _ ≤ ((2 : ℝ) ^ N * C * ((1 + D) * E ^ D)) * P *
          ((D * E ^ D) * L) ^ N := by
        apply mul_le_mul
        · exact mul_le_mul
            (mul_le_mul_of_nonneg_left houter (mul_nonneg (by positivity) hC0))
            hnP (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg (by positivity) hC0)
              (mul_nonneg (by linarith) (Real.rpow_nonneg hE0 _)))
        · exact pow_le_pow_right₀ hQ hn
        · exact pow_nonneg (zero_le_one.trans hQ) _
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (by positivity) hC0)
              (mul_nonneg (by linarith) (Real.rpow_nonneg hE0 _))) hP
      _ = A * E ^ d := by
        dsimp only [A, d]
        rw [Real.rpow_add (zero_lt_one.trans_le hE), Real.rpow_mul_natCast hE0]
        simp only [mul_pow]
        ring
  exact (hcoef.trans (hpack E hE)).trans
    (n04NegativeInverse_envelope_mono (zero_le_one.trans hB) hB₀B hE)

end ContinuousFlexibility.Analysis
