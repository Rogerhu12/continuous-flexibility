import ContinuousFlexibility.Scalar.WeightedPointwise

/-!
# Summing bounds in the actual physical jet norm

The physical norm is the square sum of its finitely many weighted L² jets.
A common bound for precisely the jets in that norm therefore gives the
explicit square-root-of-cardinality factor below.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped BigOperators ENNReal

theorem physicalNorm_le_of_weightedJet_bounds
    {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ} {s : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hmem : ∀ a b c : ℕ, a + b + c ≤ s →
      MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure)
    (hbound : ∀ a b c : ℕ, a + b + c ≤ s →
      (eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure).toReal ≤ B) :
    physicalNorm T γ s f ≤ Real.sqrt (Fintype.card (JetIndex s) : ℝ) * B := by
  classical
  let P (j : JetIndex s) : ℝ≥0∞ :=
    eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
      2 materialCylinderMeasure
  have hP (j : JetIndex s) : P j ≠ (⊤ : ℝ≥0∞) :=
    (hmem (j.val 0).val (j.val 1).val (j.val 2).val j.property).eLpNorm_ne_top
  have hPb (j : JetIndex s) : (P j).toReal ≤ B :=
    hbound (j.val 0).val (j.val 1).val (j.val 2).val j.property
  have hsum : (∑ j : JetIndex s, P j ^ 2).toReal ≤
      (Fintype.card (JetIndex s) : ℝ) * B ^ 2 := by
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top (hP j))]
    simp only [ENNReal.toReal_pow]
    calc
      _ ≤ ∑ _ : JetIndex s, B ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hPb j) 2
      _ = (Fintype.card (JetIndex s) : ℝ) * B ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change Real.sqrt (∑ j : JetIndex s, P j ^ 2).toReal ≤
    Real.sqrt (Fintype.card (JetIndex s) : ℝ) * B
  calc
    _ ≤ Real.sqrt ((Fintype.card (JetIndex s) : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card (JetIndex s) : ℝ) * B := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hB]

end ContinuousFlexibility.Statements
