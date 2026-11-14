module

public import ContinuousFlexibility.Radial.OuterDeepUniform

/-!
# A single sharp product exponent for all actual deep tails

The existing R07 proof uses the explicit constant below. Keeping this
constant outside the height, frequency, endpoint and cell quantifiers
provides the uniform input needed for localized Green estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def outerDeepProductExponent (C : ℕ → ℝ) : ℝ :=
  100 + 2 * |log (C 0)|

theorem outerDeepProductExponent_pos (C : ℕ → ℝ) :
    0 < outerDeepProductExponent C := by
  unfold outerDeepProductExponent
  positivity

/-- The explicit R07 sharp exponent depends only on the common
mass/resistance constant, not on a physical frequency or a height choice. -/
theorem outer_deepTail_product_lower
    {M : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds M σ D C) (right : Bool) {j start : ℕ}
    (hj : 2 ≤ j) (hstart : M.index < start) (h32 : 32 ≤ start) (η K : ℝ)
    (hclose : (r07DeepTailData M D right j start η K).endpoint -
      (r07DeepTailData M D right j start η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹)
    (n : ℕ) :
    let Q := r07DeepTailData M D right j start η K
    exp (2 * ((start + n : ℕ) : ℝ) ^ 2 -
      outerDeepProductExponent C *
        (((start + n : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + n : ℕ))) ≤
      Q.Λ * tailMass Q (n + 1) * tailResistance Q n := by
  have hbound := (r07_deepTail_adjacent_products h hσ hb right hj hstart h32 η K
    hclose n (n + 1) (Or.inr rfl)).2.2
  exact (r07_absorb_sharp_constant (h.constants_pos 0)
    (r07_deepTail_lambda_one_le hj) (by omega : 1 ≤ start + n)).trans hbound

/-- The same sharp constant controls the actual outer factory at its
geometrical entrance; the left initial resistance convention is unchanged. -/
theorem outer_actual_deepTail_product_lower
    {M : MorseChainData} {D : ReferenceData} {σ C : ℕ → ℝ}
    (h : MorseChainRealization M σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hb : MorseMassResistanceBounds M σ D C) (right : Bool) {j n : ℕ}
    (hj : 2 ≤ j) (hn : M.index ≤ n) (h31 : 31 ≤ n) (η K : ℝ)
    (hclose : (morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K).endpoint -
      (morsePhysicalDeepTail M D right j (n + 1)
        (morseOuterDeepEntrance M right n) η K).entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹) :
    let Q := morsePhysicalDeepTail M D right j (n + 1)
      (morseOuterDeepEntrance M right n) η K
    ∀ k : ℕ, exp (2 * ((n + 1 + k : ℕ) : ℝ) ^ 2 -
      outerDeepProductExponent C *
        (((n + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (n + 1 + k : ℕ))) ≤
      Q.Λ * tailMass Q (k + 1) * tailResistance Q k := by
  dsimp only
  rw [morsePhysicalDeepTail_eq_r07 h right j n hn η K] at hclose ⊢
  intro k
  exact outer_deepTail_product_lower h hσ hb right hj
    (hn.trans_lt (Nat.lt_succ_self n)) (by omega) η K hclose k

/-- Both the cutoff and the sharp product exponent are chosen before all
height, frequency, endpoint and cell choices. Every predicate refers to
the actual factory, not to abstract tail data with assumed estimates. -/
theorem outer_exists_uniform_actual_deepTailProduct
    (M : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData)
    (hfamily : ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
      MorseChainRealization M σ (family σ) C ∧
        MorseMassResistanceBounds M σ (family σ) C)
    (hends : ∀ σ τ, (family σ).a = (family τ).a ∧
      (family σ).b = (family τ).b)
    {Cstar η K : ℝ} (hCstar : 0 < Cstar)
    (hη : 0 < η) (hη1 : η < 1) (hK : 1 < K) (minimum : ℕ) :
    ∃ A : ℝ, 0 < A ∧
      ∃ N₀ : ℕ, minimum ≤ N₀ ∧ M.index ≤ N₀ ∧ 31 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n → ∀ σ, (∀ k, 1 ≤ σ k ∧ σ k ≤ 2) →
          ∀ j : ℕ, 2 ≤ j → (j : ℝ) < radialFrequencyThreshold M Cstar n →
            ∀ right : Bool,
              let Q := morsePhysicalDeepTail M (family σ) right j (n + 1)
                (morseOuterDeepEntrance M right n) η K
              Q.endpoint - Q.entrance ≤ (2 * (j : ℝ) ^ 2)⁻¹ ∧
                DeepTailHypotheses Q ∧
                  TailPhysicalRelation (family σ) Q right j (n + 1) ∧
                    ∀ k : ℕ, exp (2 * ((n + 1 + k : ℕ) : ℝ) ^ 2 -
                      A * (((n + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) +
                        (n + 1 + k : ℕ))) ≤
                      Q.Λ * tailMass Q (k + 1) * tailResistance Q k := by
  obtain ⟨N₀, hmin, hidx, h31, hall⟩ :=
    outer_exists_uniform_actual_deepTailPhysical M C family hfamily hends
      hCstar hη hη1 hK minimum
  refine ⟨outerDeepProductExponent C, outerDeepProductExponent_pos C,
    N₀, hmin, hidx, h31, ?_⟩
  intro n hn σ hσ j hj hjupper right
  have hQ := hall n hn σ hσ j hj hjupper right
  refine ⟨hQ.1, hQ.2.1, hQ.2.2, ?_⟩
  exact outer_actual_deepTail_product_lower (hfamily σ hσ).1 hσ (hfamily σ hσ).2
    right hj (hidx.trans hn) (h31.trans hn) η K hQ.1

end ContinuousFlexibility.Radial
