module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
public import ContinuousFlexibility.Analysis.CanonicalAuxiliaryAtomPreservation

/-!
# One positive geometry neighborhood for every auxiliary column

The selected positive pieces, geometric fields and gradings are
unchanged by auxiliary replacement. A certificate at one auxiliary
column therefore gives the same certificate at every other column.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry

private theorem positive_currentData_replaceAuxiliary
    (S : PhysicalSpacesData) (T : MaterialData) (cell : ℕ → ℕ)
    (η η' : (S.height (3 / 4 : ℝ)).Space) (P : ℕ → Prop) (b : ℕ) (ε : ℝ)
    (f : Parameter S → ℕ → PolarPoint → ℝ) (f₀ : ℕ → PolarPoint → ℝ)
    (h : CurrentJetDataOn (physicalSpacesReplaceAuxiliaryColumn S η) T cell P b ε f f₀) :
    CurrentJetDataOn (physicalSpacesReplaceAuxiliaryColumn S η') T cell P b ε f f₀ := h

namespace N04RealizationGauge

private theorem positive_atomFamily_auxiliary
    (G : N04RealizationGauge) (η η' : (G.W.S.height (3 / 4 : ℝ)).Space)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) : G.atomFamily η a = G.atomFamily η' a := by
  funext z m
  exact (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L
    (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
    η (G.lift η z) m a ha).trans
      (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L
        (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
        η' (G.lift η z) m a ha).symm

private theorem positive_atomRef_auxiliary
    (G : N04RealizationGauge) (η η' : (G.W.S.height (3 / 4 : ℝ)).Space)
    (a : Atom) (ha : a ≠ .auxiliaryColumn) : G.atomRef η a = G.atomRef η' a := by
  funext m
  exact (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L
    (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
    η (G.ref η) m a ha).trans
      (canonicalAtom_replaceAuxiliaryColumn_of_ne G.W.D G.W.U G.W.S G.W.C G.W.L
        (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
        η' (G.ref η) m a ha).symm

private theorem positive_atomData_auxiliary
    (G : N04RealizationGauge) (η η' : (G.W.S.height (3 / 4 : ℝ)).Space)
    (P : ℕ → Prop) (b : ℕ) (ε : ℝ) (a : Atom) (ha : atomIsGeometry a)
    (h : G.Data η P b ε (G.atomFamily η a) (G.atomRef η a)) :
    G.Data η' P b ε (G.atomFamily η' a) (G.atomRef η' a) := by
  have hne : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    exact ha
  have hh : G.Data η' P b ε (G.atomFamily η a) (G.atomRef η a) :=
    positive_currentData_replaceAuxiliary G.W.S G.W.U (G.V η).cell η η' P b ε
      (G.atomFamily η a) (G.atomRef η a) h
  exact (congrArg₂ (fun f f₀ => G.Data η' P b ε f f₀)
    (positive_atomFamily_auxiliary G η η' a hne)
    (positive_atomRef_auxiliary G η η' a hne)).mp hh

theorem positiveGeometry_data_auxiliary
    (G : N04RealizationGauge) (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (b : ℕ) (ε : ℝ)
    (h : G.GeometryData η₀ (G.Pos η₀) b ε) :
    G.GeometryData η (G.Pos η) b ε := by
  refine ⟨?_, h.2⟩
  intro a ha
  exact positive_atomData_auxiliary G η₀ η (G.Pos η₀) b ε a ha (h.1 a ha)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
