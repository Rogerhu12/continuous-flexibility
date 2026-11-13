import ContinuousFlexibility.Analysis.N04NegativeGeometryAuxiliary
import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit

/-!
# One negative-height neighborhood for every auxiliary column

The auxiliary replacement changes neither the selected negative pieces
nor the actual height families.  A current-data certificate obtained at
one auxiliary column therefore transfers with its entire neighborhood,
its genuine directional towers and every quantitative constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open ContinuousFlexibility.Statements CanonicalGeometry

variable (G : N04RealizationGauge)

/-- Specialize the existing non-auxiliary family identity to the zero
auxiliary column used to choose the common neighborhood. -/
theorem height_atomFamily_auxiliary_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    G.atomFamily η a = G.atomFamily 0 a :=
  G.nonAuxiliary_atomFamily_eq 0 η a ha

theorem height_atomRef_auxiliary_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    G.atomRef η a = G.atomRef 0 a :=
  G.nonAuxiliary_atomRef_eq 0 η a ha

/-- Transport actual selected-piece current data for any non-auxiliary
atom; the physical spaces, sample and parameter grading are unchanged. -/
theorem nonAuxiliary_atomData_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (P : ℕ → Prop) (b : ℕ) (ε : ℝ)
    (a : Atom) (ha : a ≠ .auxiliaryColumn)
    (h : G.Data η₀ P b ε (G.atomFamily η₀ a) (G.atomRef η₀ a)) :
    G.Data η P b ε (G.atomFamily η a) (G.atomRef η a) := by
  rw [G.nonAuxiliary_atomFamily_eq η₀ η a ha, G.nonAuxiliary_atomRef_eq η₀ η a ha]
  exact h

/-- Atom selection and the negative-piece predicate can be transferred
simultaneously without changing the neighborhood. -/
theorem negativeAtomData_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) {A : Atom → Prop}
    (hA : ∀ a, A a → a ≠ .auxiliaryColumn) (b : ℕ) (ε : ℝ)
    (h : G.NegativeAtomData η₀ A b ε) : G.NegativeAtomData η A b ε := by
  intro a ha
  exact G.nonAuxiliary_atomData_auxiliary η₀ η (G.Neg η₀) b ε a (hA a ha) (h a ha)

/-- The same height and reciprocal-height certificate works for every
auxiliary column, with no new choice of base order or radius. -/
theorem negativeHeightAtomData_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) (ε : ℝ)
    (h : G.NegativeAtomData η₀ atomIsNegativeHeight b ε) :
    G.NegativeAtomData η atomIsNegativeHeight b ε := by
  apply G.negativeAtomData_auxiliary η₀ η (b := b) (ε := ε) (h := h)
  intro a ha he
  subst a
  exact ha

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeightAtomData_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeHeightAtomData_auxiliary
