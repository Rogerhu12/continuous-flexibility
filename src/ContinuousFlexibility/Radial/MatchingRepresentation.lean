import ContinuousFlexibility.Radial.MatchedMatrixInverse
import ContinuousFlexibility.Radial.MatchingInverseFormula

/-!
# Construction of the bounded matched representation

The selected local pieces determine a bounded operator with the exact
matched formula and a uniformly controlled two-sided matching inverse.
The differential inverse properties are proved separately.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

/-- Complete the matrix field and construct the bounded operator in the
exact representation, without assuming its differential inverse properties. -/
theorem MatchedPieces.exists_actualMatchedRepresentation_with_Kinv
    (D : ReferenceData) (M : RadialMatchingData D) (h : MatchedPieces D M) :
    ∃ Kinv : RadialMatrix, ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
      ActualMatchedRepresentation D G { M with Kinv := Kinv } := by
  obtain ⟨Kinv, hbound, hleft, hright⟩ :=
    MatchedPieces.exists_matchingMatrixInverse D M h
  rcases h with
    ⟨hcutLeft, hcuts, hcutRight, hcolumn, hmargin, hdiag, herror,
      hlocal, hsymm, hoff, hnorm⟩
  let M' : RadialMatchingData D := { M with Kinv := Kinv }
  have hlocal' : MatchingLocalRealizations D M' := hlocal
  obtain ⟨G, hformula⟩ := exists_matchingFormulaCLM D M' hlocal'
  refine ⟨Kinv, G, ?_⟩
  exact ⟨hcutLeft, hcuts, hcutRight, hcolumn, hmargin, hdiag, herror,
    hbound, hlocal', hsymm, hoff, hnorm, hleft, hright, hformula⟩

/-- Retain the original public interface as a projection of the same
matrix inverse and the same matching formula. -/
theorem MatchedPieces.exists_actualMatchedRepresentation
    (D : ReferenceData) (M : RadialMatchingData D) (h : MatchedPieces D M) :
    ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
      ∃ M' : RadialMatchingData D,
        M'.frequency = M.frequency ∧ ActualMatchedRepresentation D G M' := by
  obtain ⟨Kinv, G, hactual⟩ := MatchedPieces.exists_actualMatchedRepresentation_with_Kinv D M h
  exact ⟨G, { M with Kinv := Kinv }, rfl, hactual⟩

end ContinuousFlexibility.Blueprint
