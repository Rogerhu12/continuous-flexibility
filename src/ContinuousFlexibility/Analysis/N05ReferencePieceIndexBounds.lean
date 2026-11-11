import ContinuousFlexibility.Analysis.N05ReferenceInterface
import ContinuousFlexibility.Analysis.N05MaterialCellCoordinates

/-!
# Every active reference cell is close to its physical piece index

The prescribed endpoint-coordinate comparison applies to every actual
reference cell. Two cells containing the same radius consequently have
uniformly close indices. The genuine piece-to-cell association transfers
this to every active reference localizer on a canonical physical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem n05_referenceCell_indices_at_same_radius {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ A : ℝ, 0 < A ∧ ∀ i j r, r ∈ D.cells i → r ∈ D.cells j →
      |(D.cellIndex i : ℝ) - (D.cellIndex j : ℝ)| ≤ A := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcomp⟩ := hdata
  obtain ⟨A, _, hA, _, hbound⟩ := hcomp
  refine ⟨2 * A, by positivity, fun i j r hi hj => ?_⟩
  calc
    _ ≤ |(D.cellIndex i : ℝ) - endpointX 1 (endpointDistance D r)| +
        |endpointX 1 (endpointDistance D r) - (D.cellIndex j : ℝ)| :=
      abs_sub_le _ _ _
    _ = |endpointX 1 (endpointDistance D r) - (D.cellIndex i : ℝ)| +
        |endpointX 1 (endpointDistance D r) - (D.cellIndex j : ℝ)| := by
      rw [abs_sub_comm (D.cellIndex i : ℝ)]
    _ ≤ A + A := add_le_add (hbound i r hi).1 (hbound j r hj).1
    _ = _ := by ring

theorem n05_referencePiece_cell_index_bound {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hT : IsMaterialData D T)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) → r ∈ D.cells j →
        |(D.cellIndex j : ℝ) - (D.cellIndex (K.cell m) : ℝ)| ≤ B := by
  obtain ⟨A, hA, hsame⟩ := n05_referenceCell_indices_at_same_radius hT
  obtain ⟨B, hB, hassociation, _, _⟩ := hcoordinates.2
  refine ⟨A + B, add_pos hA hB, fun m j r hr hrj => ?_⟩
  obtain ⟨i, hri, hi⟩ := hassociation m r hr
  exact (abs_sub_le (D.cellIndex j : ℝ) (D.cellIndex i : ℝ)
    (D.cellIndex (K.cell m) : ℝ)).trans (add_le_add (hsame j i r hrj hri) hi)

end ContinuousFlexibility.Statements
