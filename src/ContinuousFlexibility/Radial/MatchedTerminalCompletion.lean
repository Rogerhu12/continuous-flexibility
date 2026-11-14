module

public import ContinuousFlexibility.Blueprint.R10a.Poisson
public import ContinuousFlexibility.Radial.MatchingInverseTheorem

/-!
# Completing the same actual terminal regional data

The Poisson construction changes its three unfilled fields and the
matching formula supplies the matrix inverse. Every regional operator,
cut, scale, boundary line, cutoff and cost is retained definitionally.
The returned regional record therefore carries the actual local graph
needed by the estimates for those same operators and columns.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem TerminalRegionalData.exists_completed_actual
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (W : TerminalRegionalData D) :
    ∃ P : Fin 2 → RadialModePair D, ∃ p : Fin 2 → ℝ → ℝ,
      ∃ Db Kinv : RadialMatrix, ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        let R : TerminalRegionalData D :=
          { W with matching :=
              { W.matching with innerPoisson := P, innerFunction := p, Db := Db, Kinv := Kinv } }
        ActualMatchedRepresentation D G R.matching ∧
          ModeInverseProperties D W.matching.frequency G := by
  obtain ⟨P, p, Db, hpieces⟩ := R10aPoisson_with_fields hD hB W
  obtain ⟨Kinv, G, hactual⟩ := MatchedPieces.exists_actualMatchedRepresentation_with_Kinv
    D { W.matching with innerPoisson := P, innerFunction := p, Db := Db } hpieces
  refine ⟨P, p, Db, Kinv, G, hactual, ?_⟩
  have hmode := actualMatchedRepresentation_modeInverseProperties hD hB hactual
  exact hmode

end ContinuousFlexibility.Radial
