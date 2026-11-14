module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# Selecting one reference witness before the common neighborhood

The five physical fields in `FieldData` do not use the auxiliary column.
Once any same-atlas reference certificate exists, one such witness can
therefore be selected before the neighborhood. A theorem at that fixed
witness gives the same field data for every auxiliary column. If no
certificate exists, the conditional conclusion uses the input neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- The complete pulled-field interface is unchanged by replacing the
auxiliary column. Its fields, parameter gradings, domains and samples
are the same; no full reference certificate is transported. -/
theorem N04RealizationGauge.fieldData_auxiliary_transport
    (G : N04RealizationGauge)
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (h : G.FieldData η₀ base ε) :
    G.FieldData η base ε := h

/-- It suffices to construct the actual data at one fixed auxiliary
witness. The final neighborhood still precedes every auxiliary column
and every reference certificate, as required by the repaired obligation. -/
theorem n04PulledFields_obligation_of_fixedAuxiliary
    (hfixed : ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ),
      G.Admissible b ε → ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      G.ReferenceData η → G.GeometryData η (fun _ => True) b ε →
      ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ G.FieldData η b' ε') :
    N04RealizationPulledFieldObligation := by
  classical
  intro G b ε hadm hgeo
  by_cases hex : ∃ η : (G.W.S.height (3 / 4 : ℝ)).Space, G.ReferenceData η
  · refine hex.elim fun η₀ href => ?_
    refine (hfixed G b ε hadm η₀ href (hgeo η₀ href)).elim fun b' hb' => ?_
    refine hb'.elim fun ε' hdata => ?_
    exact ⟨b', ε', hdata.1, hdata.2.1, hdata.2.2.1,
      fun η _ => G.fieldData_auxiliary_transport η₀ η hdata.2.2.2⟩
  · exact ⟨b, ε, le_rfl, hadm.2.1, le_rfl,
      fun η href => (hex ⟨η, href⟩).elim⟩

end ContinuousFlexibility.Analysis
