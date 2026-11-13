import ContinuousFlexibility.Analysis.N04PulledFieldsMovingPointOneHigh
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Sampled material constants after moving-point composition

The finite partition count and the physical and inverse coefficient
envelopes are absorbed into the single constant of the current-jet
interface. The sampled height factor and the complete one-high weight
are retained without alteration.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

/-- Pack the entire finite moving-point coefficient, uniformly before
the sampled envelope is evaluated. No height factor is used in the pack. -/
theorem n04PulledFields_movingPoint_materialConstant
    (K s : ℕ) (C A M P L : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ E : ℝ, 1 ≤ E →
      (∑ j : Fin (K + s + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)) *
        (C * E ^ A) * (4 * (M * E ^ P) * L) ^ (K + s) ≤ B * E ^ B := by
  let count : ℝ := ∑ j : Fin (K + s + 1),
    (Fintype.card (OrderedFinpartition j.val) : ℝ)
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack
    (count * C * (4 * M * L) ^ (K + s)) (A + P * (K + s : ℕ))
  refine ⟨B, hB, fun E hE => ?_⟩
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have heq : count * (C * E ^ A) * (4 * (M * E ^ P) * L) ^ (K + s) =
      (count * C * (4 * M * L) ^ (K + s)) * E ^ (A + P * (K + s : ℕ)) := by
    rw [show 4 * (M * E ^ P) * L = (4 * M * L) * E ^ P by ring, mul_pow,
      ← Real.rpow_mul_natCast hEpos.le, Real.rpow_add hEpos]
    ring
  exact heq.trans_le (hpack E hE)

/-- A normalized genuine jet with the finite composition coefficient
has exactly the sampled coefficient form required by current data. -/
theorem n04PulledFields_movingPoint_materialOneHigh
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (K s : ℕ) (C A M P L : ℝ)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ E H : ℝ, 1 ≤ E → 0 ≤ H →
      ∀ k : ℕ, ∀ x : X, ∀ v : Fin k → X, ∀ value : ℝ,
      |value| ≤
        (∑ j : Fin (K + s + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)) *
          (C * E ^ A) * (4 * (M * E ^ P) * L) ^ (K + s) * H *
            oneHighVariationWeight p base high x v →
      |value| ≤ B * E ^ B * H * oneHighVariationWeight p base high x v := by
  obtain ⟨B, hB, hpack⟩ := n04PulledFields_movingPoint_materialConstant K s C A M P L
  refine ⟨B, hB, fun E H hE hH k x v value hvalue => ?_⟩
  exact hvalue.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hpack E hE) hH)
    (oneHighVariationWeight_nonneg p base high x v))

end ContinuousFlexibility.Analysis
