module

public import ContinuousFlexibility.Analysis.PhysicalGradeEnergy

/-!
# Finite physical jet sums with arbitrary component weights

This is a finite-index calculation in the nonnegative extended reals.
Component weights stay outside the actual L2 norms. A common bound for
every jet of total order at most s controls the sum of all levels up to s.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped ENNReal BigOperators

theorem physicalLevelEnergy_weighted_tsum_le
    {T : MaterialData} {γ : ℝ} (w : ℕ → ℝ≥0∞)
    (f : ℕ → PolarPoint → ℝ) (s : ℕ) (Q : ℝ≥0∞)
    (hjet : ∀ a b c : ℕ, a + b + c ≤ s →
      (∑' m : ℕ, w m * eLpNorm (weightedPhysicalJet T γ a b c (f m))
        2 materialCylinderMeasure ^ 2) ≤ Q) :
    (∑' m : ℕ, w m * physicalLevelEnergy T γ s (f m)) ≤
      (Fintype.card (JetIndex s) : ℝ≥0∞) * Q := by
  classical
  have hcomm : (∑' m : ℕ, w m * physicalLevelEnergy T γ s (f m)) =
      ∑ j : JetIndex s, ∑' m : ℕ,
        w m * eLpNorm (weightedPhysicalJet T γ
          (j.val 0).val (j.val 1).val (j.val 2).val (f m))
          2 materialCylinderMeasure ^ 2 := by
    simpa only [physicalLevelEnergy, Finset.mul_sum, tsum_fintype] using
      ENNReal.tsum_comm (f := fun m (j : JetIndex s) =>
        w m * eLpNorm (weightedPhysicalJet T γ
          (j.val 0).val (j.val 1).val (j.val 2).val (f m))
          2 materialCylinderMeasure ^ 2)
  rw [hcomm]
  calc
    _ ≤ ∑ _j : JetIndex s, Q :=
      Finset.sum_le_sum (fun j _ => hjet _ _ _ j.property)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem physicalLevelEnergy_cumulative_weighted_tsum_le
    {T : MaterialData} {γ : ℝ} (w : ℕ → ℝ≥0∞)
    (f : ℕ → PolarPoint → ℝ) (s : ℕ) (Q : ℝ≥0∞)
    (hjet : ∀ a b c : ℕ, a + b + c ≤ s →
      (∑' m : ℕ, w m * eLpNorm (weightedPhysicalJet T γ a b c (f m))
        2 materialCylinderMeasure ^ 2) ≤ Q) :
    (∑' m : ℕ, w m * ∑ i : Fin (s + 1), physicalLevelEnergy T γ i.val (f m)) ≤
      ((∑ i : Fin (s + 1), Fintype.card (JetIndex i.val) : ℕ) : ℝ≥0∞) * Q := by
  classical
  have hcomm :
      (∑' m : ℕ, w m * ∑ i : Fin (s + 1), physicalLevelEnergy T γ i.val (f m)) =
      ∑ i : Fin (s + 1), ∑' m : ℕ, w m * physicalLevelEnergy T γ i.val (f m) := by
    simpa only [Finset.mul_sum, tsum_fintype] using
      ENNReal.tsum_comm (f := fun m (i : Fin (s + 1)) =>
        w m * physicalLevelEnergy T γ i.val (f m))
  rw [hcomm]
  calc
    _ ≤ ∑ i : Fin (s + 1), (Fintype.card (JetIndex i.val) : ℝ≥0∞) * Q := by
      apply Finset.sum_le_sum
      intro i hi
      exact physicalLevelEnergy_weighted_tsum_le w f i.val Q
        (fun a b c horder => hjet a b c (horder.trans (Nat.le_of_lt_succ i.isLt)))
    _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum]

end ContinuousFlexibility.Statements
