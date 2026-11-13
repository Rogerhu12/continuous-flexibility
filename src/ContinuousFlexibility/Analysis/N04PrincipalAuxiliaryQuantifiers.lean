import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# The auxiliary-column quantifier in the principal obligation

Principal atoms do not contain the auxiliary column. A neighborhood
constructed using one reference-jet witness therefore serves every
auxiliary column. If no reference witness exists, the final implications
are vacuous. This keeps the neighborhood before the auxiliary column in
the unchanged blueprint statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

namespace N04RealizationGauge

/-- All eight principal atoms, their parameter spaces and their weights
are unchanged by auxiliary-column replacement. -/
theorem n04Principal_data_auxiliary
    (G : N04RealizationGauge)
    (η η' : (G.W.S.height (3 / 4 : ℝ)).Space)
    (P : ℕ → Prop) (b : ℕ) (ε : ℝ) (a : Atom) (ha : atomIsPrincipal a)
    (h : G.Data η P b ε (G.atomFamily η a) (G.atomRef η a)) :
    G.Data η' P b ε (G.atomFamily η' a) (G.atomRef η' a) := by
  cases a <;> first
    | exact ha.elim
    | exact h

end N04RealizationGauge

/-- The analytical problem for one fixed auxiliary column. The theorem
below restores the original quantifier order without any uniformity
assumption about the supplied reference certificates. -/
def N04PrincipalFixedAuxiliaryObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    ∀ η, G.GeometryData η (fun _ => True) b ε → G.FieldData η b ε →
      ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) →
      ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
        ∀ a : Atom, atomIsPrincipal a →
          G.Data η (fun _ => True) b' ε' (G.atomFamily η a) (G.atomRef η a)

/-- Proving the fixed-column analytical statement is enough for the exact
principal obligation. The selected neighborhood is reused verbatim. -/
theorem n04Principal_obligation_of_fixedAuxiliary
    (hfixed : N04PrincipalFixedAuxiliaryObligation) : N04RealizationPrincipalObligation := by
  intro G b ε hA hG hF
  classical
  by_cases href : ∃ η, ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
  · let η := href.choose
    have hlocal := hfixed G b ε hA η (hG η) (hF η) href.choose_spec
    let b' : ℕ := hlocal.choose
    let ε' : ℝ := hlocal.choose_spec.choose
    have hproof := hlocal.choose_spec.choose_spec
    refine ⟨b', ε', hproof.1, hproof.2.1, hproof.2.2.1, ?_⟩
    intro η' _ a ha
    exact G.n04Principal_data_auxiliary η η' (fun _ => True) b' ε' a ha
      (hproof.2.2.2 a ha)
  · refine ⟨b, ε, le_rfl, hA.2.1, le_rfl, ?_⟩
    intro η hη
    exact False.elim (href ⟨η, hη⟩)

end ContinuousFlexibility.Analysis
