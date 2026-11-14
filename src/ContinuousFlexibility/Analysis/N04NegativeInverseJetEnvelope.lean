module

public import ContinuousFlexibility.Analysis.N04NegativeInverseJetBudget
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Uniform material envelopes for the finite inverse majorants

The sharp mixed inverse recurrence has a finite polynomial constant at
every requested order. Its degree in a common coefficient envelope is
independent of the interpolation scale and of every direction. This
module packages those constants into the frozen `B * E ^ B` form.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

def n04NegativeInverse_partitionCount (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, (Fintype.card (Finset (Fin c.length)) : ℝ)

theorem n04NegativeInverse_partitionCount_nonneg (n : ℕ) :
    0 ≤ n04NegativeInverse_partitionCount n :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Bounding all original factors by a common envelope gives a finite
power bound for one exact partition sum. -/
theorem n04NegativeInverse_partitionMajorant_le_power
    (n d : ℕ) {C M L Q b : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L) (hQ : 1 ≤ Q) (hb : 1 ≤ b)
    (hCQ : C ≤ Q) (hMQ : M ≤ b * Q ^ d) (hLQ : L ≤ Q) :
    n04NegativeInverse_partitionMajorant C M L n ≤
      n04NegativeInverse_partitionCount n * (b ^ n * Q ^ (1 + (d + 1) * n)) := by
  classical
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  unfold n04NegativeInverse_partitionMajorant n04NegativeInverse_partitionCount
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    C * M ^ c.length * L ^ c.length ≤
        Q * (b * Q ^ d) ^ c.length * Q ^ c.length :=
      mul_le_mul
        (mul_le_mul hCQ (pow_le_pow_left₀ hM hMQ _) (pow_nonneg hM _) hQ0)
        (pow_le_pow_left₀ hL hLQ _) (pow_nonneg hL _)
        (mul_nonneg hQ0 (pow_nonneg (mul_nonneg hb0 (pow_nonneg hQ0 _)) _))
    _ = b ^ c.length * Q ^ (1 + (d + 1) * c.length) := by
      simp only [mul_pow, Nat.add_mul, Nat.one_mul, pow_add, pow_one, pow_mul]
      ring
    _ ≤ b ^ n * Q ^ (1 + (d + 1) * n) :=
      mul_le_mul (pow_le_pow_right₀ hb c.length_le)
        (pow_le_pow_right₀ hQ (Nat.add_le_add_left (Nat.mul_le_mul_left (d + 1) c.length_le) 1))
        (pow_nonneg hQ0 _) (pow_nonneg hb0 _)

/-- The recursive inverse constant is a finite power of a common
coefficient bound. Both the power and the multiplier depend only on
the requested finite order. -/
theorem n04NegativeInverse_prefixMajorant_polynomial (N : ℕ) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ d : ℕ, 1 ≤ d ∧
      ∀ Q : ℝ, 1 ≤ Q → ∀ a C L : ℝ,
      0 ≤ a → 0 ≤ C → 0 ≤ L → a ≤ Q → C ≤ Q → L ≤ Q →
      n04NegativeInverse_prefixMajorant a C L N ≤ b * Q ^ d := by
  induction N with
  | zero =>
    refine ⟨1, le_rfl, 1, le_rfl, ?_⟩
    intro Q hQ a C L _ _ _ _ _ _
    simpa only [n04NegativeInverse_prefixMajorant, pow_one, one_mul] using hQ
  | succ n ih =>
    obtain ⟨b, hb, d, hd, hbound⟩ := ih
    let count := n04NegativeInverse_partitionCount (n + 1)
    let b' : ℝ := b + 2 + count * b ^ (n + 1)
    let d' : ℕ := 2 + (d + 1) * (n + 1)
    have hcount : 0 ≤ count := n04NegativeInverse_partitionCount_nonneg (n + 1)
    have hb0 : 0 ≤ b := zero_le_one.trans hb
    have hb' : 1 ≤ b' := by
      have hs := mul_nonneg hcount (pow_nonneg hb0 (n + 1))
      dsimp only [b']
      linarith
    have hd' : 1 ≤ d' := by dsimp only [d']; omega
    have hdd' : d ≤ d' := by
      have hm : d + 1 ≤ (d + 1) * (n + 1) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (d + 1) (Nat.succ_le_succ (Nat.zero_le n))
      dsimp only [d']
      omega
    have htwo : 2 ≤ d' := by dsimp only [d']; omega
    refine ⟨b', hb', d', hd', ?_⟩
    intro Q hQ a C L ha hC hL haQ hCQ hLQ
    have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
    have hM0 : 0 ≤ n04NegativeInverse_prefixMajorant a C L n :=
      zero_le_one.trans (n04NegativeInverse_prefixMajorant_one_le ha hC hL n)
    have hM := hbound Q hQ a C L ha hC hL haQ hCQ hLQ
    have hprev : n04NegativeInverse_prefixMajorant a C L n ≤ b * Q ^ d' :=
      hM.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ hdd') hb0)
    have hfirst : a * (C + 1) ≤ 2 * Q ^ d' := by
      have hCQ₁ : C + 1 ≤ Q + 1 := by linarith
      calc
        _ ≤ Q * (Q + 1) := mul_le_mul haQ hCQ₁ (by linarith) hQ0
        _ ≤ 2 * Q ^ 2 := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ htwo) (by norm_num)
    have hp := n04NegativeInverse_partitionMajorant_le_power (n + 1) d
      hC hM0 hL hQ hb hCQ hM hLQ
    have hlast : a * n04NegativeInverse_partitionMajorant C
        (n04NegativeInverse_prefixMajorant a C L n) L (n + 1) ≤
          (count * b ^ (n + 1)) * Q ^ d' := by
      calc
        _ ≤ Q * (count * (b ^ (n + 1) * Q ^ (1 + (d + 1) * (n + 1)))) :=
          mul_le_mul haQ hp
            (n04NegativeInverse_partitionMajorant_nonneg hC hM0 hL _) hQ0
        _ = _ := by
          have he : d' = (1 + (d + 1) * (n + 1)) + 1 := by dsimp only [d']; omega
          rw [he, pow_succ]
          ring
    calc
      _ = n04NegativeInverse_prefixMajorant a C L n + a * (C + 1) +
          a * n04NegativeInverse_partitionMajorant C
            (n04NegativeInverse_prefixMajorant a C L n) L (n + 1) := rfl
      _ ≤ b * Q ^ d' + 2 * Q ^ d' + (count * b ^ (n + 1)) * Q ^ d' :=
        add_le_add (add_le_add hprev hfirst) hlast
      _ = b' * Q ^ d' := by dsimp only [b']; ring

/-- A common material envelope for the spatial inverse, the forward
jets and the height envelope controls the complete finite recurrence. -/
theorem n04NegativeInverse_prefixMajorant_envelope (N : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ E : ℝ, 1 ≤ E → ∀ a C L : ℝ,
      0 ≤ a → 0 ≤ C → 0 ≤ L →
      a ≤ B * E ^ B → C ≤ B * E ^ B → L ≤ B * E ^ B →
      n04NegativeInverse_prefixMajorant a C L N ≤ D * E ^ D := by
  obtain ⟨b, hb, d, _, hpoly⟩ := n04NegativeInverse_prefixMajorant_polynomial N
  obtain ⟨D, hD, hpack⟩ := coefficientEnvelope_pack (b * B ^ d) (B * (d : ℝ))
  refine ⟨D, hD, ?_⟩
  intro E hE a C L ha hC hL haB hCB hLB
  have hQ : 1 ≤ B * E ^ B :=
    one_le_mul_of_one_le_of_one_le hB (Real.one_le_rpow hE (zero_le_one.trans hB))
  have h := hpoly (B * E ^ B) hQ a C L ha hC hL haB hCB hLB
  have he : b * (B * E ^ B) ^ d = (b * B ^ d) * E ^ (B * (d : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
    ring
  exact (h.trans_eq he).trans (hpack E hE)

/-- The same envelope closure applies to the pulled-height graph sum. -/
theorem n04NegativeInverse_partitionMajorant_envelope (n : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ E : ℝ, 1 ≤ E → ∀ C M L : ℝ,
      0 ≤ C → 0 ≤ M → 0 ≤ L →
      C ≤ B * E ^ B → M ≤ B * E ^ B → L ≤ B * E ^ B →
      n04NegativeInverse_partitionMajorant C M L n ≤ D * E ^ D := by
  let d : ℕ := 1 + (1 + 1) * n
  obtain ⟨D, hD, hpack⟩ := coefficientEnvelope_pack
    (n04NegativeInverse_partitionCount n * B ^ d) (B * (d : ℝ))
  refine ⟨D, hD, ?_⟩
  intro E hE C M L hC hM hL hCB hMB hLB
  have hQ : 1 ≤ B * E ^ B :=
    one_le_mul_of_one_le_of_one_le hB (Real.one_le_rpow hE (zero_le_one.trans hB))
  have h := n04NegativeInverse_partitionMajorant_le_power n 1 hC hM hL hQ le_rfl hCB
    (by simpa only [one_mul, pow_one] using hMB) hLB
  simp only [one_pow, one_mul] at h
  have he : n04NegativeInverse_partitionCount n * (B * E ^ B) ^ d =
      (n04NegativeInverse_partitionCount n * B ^ d) * E ^ (B * (d : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
    ring
  exact (h.trans_eq he).trans (hpack E hE)

/-- A fixed height envelope is absorbed once into the common material
coefficient; the raw interpolation degree is unaffected. -/
theorem n04NegativeInverse_prefixMajorant_envelope_fixed_height
    (N : ℕ) {B L : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) :
    ∃ D : ℝ, 0 < D ∧ ∀ E : ℝ, 1 ≤ E → ∀ a C : ℝ,
      0 ≤ a → 0 ≤ C → a ≤ B * E ^ B → C ≤ B * E ^ B →
      n04NegativeInverse_prefixMajorant a C L N ≤ D * E ^ D := by
  let B' := max B L
  have hB' : 1 ≤ B' := hB.trans (le_max_left _ _)
  obtain ⟨D, hD, hbound⟩ := n04NegativeInverse_prefixMajorant_envelope N hB'
  refine ⟨D, hD, ?_⟩
  intro E hE a C ha hC haB hCB
  have hBB' : B * E ^ B ≤ B' * E ^ B' :=
    mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB')
  have hLB' : L ≤ B' * E ^ B' :=
    (le_max_right B L).trans (le_mul_of_one_le_right (zero_le_one.trans hB')
      (Real.one_le_rpow hE (zero_le_one.trans hB')))
  exact hbound E hE a C L ha hC (zero_le_one.trans hL)
    (haB.trans hBB') (hCB.trans hBB') hLB'

end ContinuousFlexibility.Analysis
