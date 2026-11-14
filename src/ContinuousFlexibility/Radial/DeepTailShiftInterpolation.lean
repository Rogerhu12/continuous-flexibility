module

public import ContinuousFlexibility.Radial.DeepTailInterpolation
public import ContinuousFlexibility.Radial.DeepTailShift

/-!
# Square integrability on a shifted tail

The edge estimates and square-summable original node sequence can be
reindexed without changing the physical density or interpolation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem deepTail_memLp_shift_of_edge_square_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (k : ℕ) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Ioo (T.node 0) T.endpoint))
    (huEdge : ∀ n, ContinuousOn u (Icc (T.node n) (T.node (n + 1))))
    {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, (∫ x in T.node n..T.node (n + 1), T.p x * u x ^ 2) ≤
      C * (tailMass T n * a n ^ 2 + tailMass T (n + 1) * a (n + 1) ^ 2))
    (hsum : Summable (fun n => tailMass T n * a n ^ 2)) :
    MemLp u 2 (deepTailMeasure (deepTailShift T k)) := by
  refine deepTail_memLp_of_edge_square_bound (deepTailHypotheses_shift hT k)
    (by simp only [deepTailShift, Nat.add_zero])
    (a := fun n => a (k + n)) (C := C) ?_ ?_ hC ?_ ?_
  · apply hu.mono
    intro x hx
    exact ⟨((deepTail_node_strictMono hT).monotone (Nat.zero_le k)).trans_lt hx.1, hx.2⟩
  · intro n
    simpa only [deepTailShift, Nat.add_assoc] using huEdge (k + n)
  · intro n
    simpa only [tailMass, deepTailShift, Nat.add_assoc] using hbound (k + n)
  · simpa only [tailMass_deepTailShift, Nat.add_comm k] using
      (summable_nat_add_iff k).mpr hsum

end ContinuousFlexibility.Radial
