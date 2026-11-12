import ContinuousFlexibility.Statements.Analysis

/-!
# Index comparison for actual intersecting material cells

The endpoint-coordinate clause of the actual material data bounds the
index difference of any two cells containing the same physical point.
The bound is chosen before either cell, so a genuine component host
can be compared with the retained model label at an interior point.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- Actual cell overlap gives a uniform additive index bound. -/
theorem materialCell_overlap_index_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j : ℕ, ∀ r : ℝ,
      r ∈ D.cells m → r ∈ D.cells j →
        |(D.cellIndex m : ℝ) - D.cellIndex j| ≤ B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcell⟩ := hT
  obtain ⟨C, A, hC, hA, hindex⟩ := hcell
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro m j r hrm hrj
  have hm := (hindex m r hrm).1
  have hj := (hindex j r hrj).1
  calc
    |(D.cellIndex m : ℝ) - D.cellIndex j|
      ≤ |(D.cellIndex m : ℝ) -
            ContinuousFlexibility.Analysis.endpointX 1 (endpointDistance D r)| +
          |ContinuousFlexibility.Analysis.endpointX 1 (endpointDistance D r) -
            D.cellIndex j| := abs_sub_le _ _ _
    _ ≤ C + C := add_le_add (by simpa only [abs_sub_comm] using hm) hj
    _ = 2 * C := (two_mul C).symm

end ContinuousFlexibility.Statements
