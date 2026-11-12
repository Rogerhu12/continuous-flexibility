import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
import ContinuousFlexibility.Analysis.N05OpticalNegativeGeometry
import ContinuousFlexibility.Analysis.N05ReferenceNegativeCoefficient
import ContinuousFlexibility.Analysis.N05ReferencePieceIndexBounds
import ContinuousFlexibility.Analysis.N05ReferencePieceCoefficients

/-!
# Actual negative-piece labels and their coefficient bounds

A cell selected at an interior point of a negative physical piece meets
the genuine carrier of its whole component. The material coordinate
comparison therefore transfers both the index association and the five
first-geometry bounds to that selected cell. The label certificate records
an actual intersection, without assuming any quantitative chart estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- The cell assigned to each negative piece contains one physical point
of that piece. A midpoint selection supplies this literal certificate. -/
def N05NegativePieceCellLabels (D : ReferenceData) (S : PhysicalSpacesData)
    (K : CanonicalData S) : Prop :=
  ∀ i : ℕ, K.positive i = false →
    (Ioo (K.physicalLeft i) (K.physicalRight i) ∩ D.cells (K.cell i)).Nonempty

theorem n05_cut_physical_open_subset_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε) (m : ℕ) (right : Bool) :
    Ioo (K.physicalLeft (if right then (K.cutPair m).2 else (K.cutPair m).1))
        (K.physicalRight (if right then (K.cutPair m).2 else (K.cutPair m).1)) ⊆
      Ioo (C.left m) (C.right m) := by
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  have hwidth : K.physicalLeft i < K.physicalRight i := (h04.1.referenceBounds i).1
  have hsub := n05_cut_physical_closed_subset_component h04 m right
  have hl := hsub (show K.physicalLeft i ∈ Icc (K.physicalLeft i) (K.physicalRight i)
    from ⟨le_rfl, hwidth.le⟩)
  have hr := hsub (show K.physicalRight i ∈ Icc (K.physicalLeft i) (K.physicalRight i)
    from ⟨hwidth.le, le_rfl⟩)
  exact Ioo_subset_Ioo hl.1 hr.2

/-- A genuine point label suffices for the negative part of the N05
coordinate bounds. All constants precede the piece, the point and the
angular coordinate; the actual carrier is chosen only once per component. -/
theorem n05_negative_reference_geometry_at_selected_cells
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hoptical : N05ActualCarrierOpticalLower D C)
    (hlabels : N05NegativePieceCellLabels D S K) :
    ∃ B A window : ℝ, 0 < B ∧ 0 < A ∧ 0 < window ∧
      ∀ i : ℕ, K.positive i = false →
        (∀ j r, r ∈ Ioo (K.physicalLeft i) (K.physicalRight i) → r ∈ D.cells j →
          |(D.cellIndex j : ℝ) - (D.cellIndex (K.cell i) : ℝ)| ≤ window) ∧
        (∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ : ℝ,
          n05NegativeReferenceFirstSize S C K i r θ ≤
            B * radialE (D.cellIndex (K.cell i)) ^ A) := by
  obtain ⟨B, A, hB, hA, hgeometry⟩ :=
    n05_negative_reference_first_geometry_of_actualCarrierLower hD hT hS h hoptical
  obtain ⟨window, hwindow, hsame⟩ := n05_referenceCell_indices_at_same_radius hT
  obtain ⟨P, hP, hshift⟩ := n05_radialE_power_index_window A window hA.le
  refine ⟨B * P, P, 2 * window, mul_pos hB hP, hP, by positivity, ?_⟩
  intro i hi
  have hhalf : ∃ m : ℕ, ∃ right : Bool,
      i = if right then (K.cutPair m).2 else (K.cutPair m).1 := by
    obtain ⟨m, hm⟩ := n05_negative_piece_is_cut_half h.1.1.1.2.2.2.1 h.2.2.2.2.1 hi
    rcases hm with hm | hm
    · exact ⟨m, false, hm⟩
    · exact ⟨m, true, hm⟩
  obtain ⟨m, right, rfl⟩ := hhalf
  let i := if right then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨j, hcarrier, hbound⟩ := hgeometry m
  have hsub := n05_cut_physical_open_subset_component h.2.2.2.2.1 m right
  obtain ⟨r₀, hr₀, hr₀cell⟩ := hlabels i hi
  have hindex : |(D.cellIndex j : ℝ) - (D.cellIndex (K.cell i) : ℝ)| ≤ window :=
    hsame j (K.cell i) r₀ (hcarrier (hsub hr₀)) hr₀cell
  refine ⟨?_, ?_⟩
  · intro k r hr hrk
    calc
      _ ≤ |(D.cellIndex k : ℝ) - (D.cellIndex j : ℝ)| +
          |(D.cellIndex j : ℝ) - (D.cellIndex (K.cell i) : ℝ)| := abs_sub_le _ _ _
      _ ≤ window + window := add_le_add (hsame k j r hrk (hcarrier (hsub hr))) hindex
      _ = 2 * window := by ring
  · intro r hr θ
    calc
      n05NegativeReferenceFirstSize S C K i r θ ≤ B * radialE (D.cellIndex j) ^ A :=
        hbound right r hr θ
      _ ≤ B * (P * radialE (D.cellIndex (K.cell i)) ^ P) :=
        mul_le_mul_of_nonneg_left (hshift (D.cellIndex j) (D.cellIndex (K.cell i)) hindex) hB.le
      _ = (B * P) * radialE (D.cellIndex (K.cell i)) ^ P := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Statements
