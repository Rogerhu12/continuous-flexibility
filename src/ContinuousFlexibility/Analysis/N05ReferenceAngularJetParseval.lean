module

public import ContinuousFlexibility.Analysis.N05ReferenceAngularJetCells
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Weighted Parseval for actual finite angular jets

This identity uses any radial cell weights. Individual singleton series
suffice for summability of the finite derivative field, so no extra
derivative membership assumption is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem n05_referenceHighAngularJet_weighted_sum {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (J : Finset ℕ) (b : ℕ) (w : ℕ → ℝ)
    (hs : ∀ n ∈ J, Summable (fun m =>
      w m * referenceCellSquare D m (referenceBasisProjection {n + 2} f))) :
    RadialCellIntegrable D (n05_referenceHighAngularJet J b f) ∧
      Summable (fun m => w m *
        referenceCellSquare D m (n05_referenceHighAngularJet J b f)) ∧
      (∑' m, w m * referenceCellSquare D m (n05_referenceHighAngularJet J b f)) =
        ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          ∑' m, w m * referenceCellSquare D m (referenceBasisProjection {n + 2} f) := by
  have hsi (n : ℕ) (hn : n ∈ J) : Summable (fun m =>
      (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        (w m * referenceCellSquare D m (referenceBasisProjection {n + 2} f))) :=
    (hs n hn).mul_left _
  have heq (m : ℕ) :
      w m * referenceCellSquare D m (n05_referenceHighAngularJet J b f) =
        ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          (w m * referenceCellSquare D m (referenceBasisProjection {n + 2} f)) := by
    rw [n05_referenceHighAngularJet_cell_square hab hf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  refine ⟨(n05_referenceHighAngularJet_cell_parseval hab hf J b).1, ?_, ?_⟩
  · simpa only [heq] using summable_sum hsi
  · calc
      (∑' m, w m * referenceCellSquare D m (n05_referenceHighAngularJet J b f)) =
          ∑' m, ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
            (w m * referenceCellSquare D m (referenceBasisProjection {n + 2} f)) :=
        tsum_congr heq
      _ = ∑ n ∈ J, ∑' m, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
            (w m * referenceCellSquare D m (referenceBasisProjection {n + 2} f)) :=
        Summable.tsum_finsetSum hsi
      _ = _ := by simp only [tsum_mul_left]

end ContinuousFlexibility.Radial
