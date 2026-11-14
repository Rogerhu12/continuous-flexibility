module

public import ContinuousFlexibility.Analysis.N05ReferenceInterface
public import ContinuousFlexibility.Analysis.N05MaterialCellCoordinates
public import ContinuousFlexibility.Analysis.N05ReferenceSourceWeightGap

/-!
# Every active reference cell satisfies the endpoint-exponent window

The prescribed endpoint-coordinate comparison applies to every actual
reference cell. Two cells containing the same radius consequently have
uniformly close indices. Combining that overlap estimate with the genuine
association transfers the endpoint-exponent window to every active reference
localizer on a canonical physical piece.
-/

@[expose] public section

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

theorem n05_referencePiece_cell_swindow {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    (hT : IsMaterialData D T)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) → r ∈ D.cells j →
        |radialS (D.cellIndex j) - radialS (D.cellIndex (K.cell m))| ≤
          B * (radialQ (D.cellIndex (K.cell m)) + 1) := by
  obtain ⟨A, hA, hsame⟩ := n05_referenceCell_indices_at_same_radius hT
  obtain ⟨B, hB, hassociation, _, _⟩ := hcoordinates.2
  obtain ⟨Q, hQ, hq⟩ := n05_radialQ_swindow_bound hB.le
  let P : ℝ := 6 * A * (A ^ 2 + 1)
  have hP : 0 < P := by dsimp only [P]; positivity
  refine ⟨P * (Q + 1) + B, by positivity, fun m j r hr hrj => ?_⟩
  obtain ⟨i, hri, hi⟩ := hassociation m r hr
  have hji : |radialS (D.cellIndex j) - radialS (D.cellIndex i)| ≤
      P * (radialQ (D.cellIndex i) + 1) :=
    n05_radialS_index_window hA.le _ _ (hsame j i r hrj hri)
  have hqbound := hq (D.cellIndex i) (D.cellIndex (K.cell m)) hi
  have hqadd : radialQ (D.cellIndex i) + 1 ≤
      (Q + 1) * (radialQ (D.cellIndex (K.cell m)) + 1) := by
    have hn := Radial.radialQ_nonneg (D.cellIndex (K.cell m))
    nlinarith only [hqbound, hn]
  calc
    _ ≤ |radialS (D.cellIndex j) - radialS (D.cellIndex i)| +
        |radialS (D.cellIndex i) - radialS (D.cellIndex (K.cell m))| :=
      abs_sub_le _ _ _
    _ ≤ P * (radialQ (D.cellIndex i) + 1) +
        B * (radialQ (D.cellIndex (K.cell m)) + 1) := add_le_add hji hi
    _ ≤ P * ((Q + 1) * (radialQ (D.cellIndex (K.cell m)) + 1)) +
        B * (radialQ (D.cellIndex (K.cell m)) + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hqadd hP.le) (le_refl _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
