module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation

/-!
# Auxiliary-column independence of negative geometry

The geometric atoms and pulled height use only the atlas fields preserved
by auxiliary-column replacement. Consequently one neighborhood proved at
the zero auxiliary column works for every auxiliary column, with exactly
the same selected-piece towers and estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open ContinuousFlexibility.Statements CanonicalGeometry

variable (G : N04RealizationGauge)

/-- The complete current scalar family of a non-auxiliary atom is
preserved, before selecting any jets or directional towers. -/
theorem nonAuxiliary_atomFamily_eq
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    G.atomFamily η a = G.atomFamily η₀ a := by
  funext z m
  let K := n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N
  exact (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L K
    η (liftSectorParameter G.W.S G.W.C z) m a ha).trans
      (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L K
        η₀ (liftSectorParameter G.W.S G.W.C z) m a ha).symm

/-- The reference scalar family is preserved by the same field identity. -/
theorem nonAuxiliary_atomRef_eq
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) :
    G.atomRef η a = G.atomRef η₀ a := by
  funext m
  let K := n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N
  exact (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L K
    η (G.W.C.referenceState, 0) m a ha).trans
      (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L K
        η₀ (G.W.C.referenceState, 0) m a ha).symm

/-- Transport a geometric atom's selected-piece data between auxiliary columns. -/
theorem geometryAtom_data_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (P : ℕ → Prop) (b : ℕ) (ε : ℝ)
    (a : Atom) (ha : atomIsGeometry a) :
    G.Data η₀ P b ε (G.atomFamily η₀ a) (G.atomRef η₀ a) →
      G.Data η P b ε (G.atomFamily η a) (G.atomRef η a) := by
  intro h
  have hne : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    exact ha
  rw [G.nonAuxiliary_atomFamily_eq η₀ η a hne, G.nonAuxiliary_atomRef_eq η₀ η a hne]
  exact h

/-- The pulled-height data is independent of the auxiliary column. -/
theorem pulledHeight_data_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (P : ℕ → Prop) (b : ℕ) (ε : ℝ) :
    G.Data η₀ P b ε (G.pulledHeight η₀) (G.pulledHeightRef η₀) →
      G.Data η P b ε (G.pulledHeight η) (G.pulledHeightRef η) := by
  intro h
  exact h

/-- A single geometry certificate supplies all auxiliary columns. -/
theorem geometryData_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (P : ℕ → Prop) (b : ℕ) (ε : ℝ)
    (h : G.GeometryData η₀ P b ε) : G.GeometryData η P b ε :=
  ⟨fun a ha => G.geometryAtom_data_auxiliary η₀ η P b ε a ha (h.1 a ha),
    G.pulledHeight_data_auxiliary η₀ η P b ε h.2⟩

/-- In particular, the negative-piece certificate transfers unchanged. -/
theorem negativeGeometryData_auxiliary
    (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space) (b : ℕ) (ε : ℝ)
    (h : G.GeometryData η₀ (G.Neg η₀) b ε) : G.GeometryData η (G.Neg η) b ε :=
  G.geometryData_auxiliary η₀ η (G.Neg η₀) b ε h

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeGeometryData_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeGeometryData_auxiliary
