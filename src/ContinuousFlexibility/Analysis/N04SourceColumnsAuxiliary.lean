module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# Auxiliary-column independence of the four source outputs

Changing the auxiliary column preserves the spaces, gradings, chart,
height and the two physical scalar columns used here.  The complete
reference-jet hypothesis is not transported, since it also contains the
auxiliary atom itself.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open ContinuousFlexibility.Statements CanonicalGeometry

variable (G : N04RealizationGauge)

theorem sourceColumns_data_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) (ε : ℝ)
    (a : Atom) (ha : atomIsSourceColumn a) :
    G.Data η₀ (fun _ => True) b ε (G.atomFamily η₀ a) (G.atomRef η₀ a) →
      G.Data η (fun _ => True) b ε (G.atomFamily η a) (G.atomRef η a) := by
  intro h
  cases a <;> first
    | exact False.elim ha
    | exact h

end ContinuousFlexibility.Analysis.N04RealizationGauge
