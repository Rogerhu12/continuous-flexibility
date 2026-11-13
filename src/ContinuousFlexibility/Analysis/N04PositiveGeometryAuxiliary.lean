import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# One positive geometry neighborhood for every auxiliary column

The selected positive pieces, geometric fields and gradings are
unchanged by auxiliary replacement. A certificate at one auxiliary
column therefore gives the same certificate at every other column.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open ContinuousFlexibility.Statements CanonicalGeometry

theorem positiveGeometry_data_auxiliary
    (G : N04RealizationGauge) (η₀ η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (b : ℕ) (ε : ℝ)
    (h : G.GeometryData η₀ (G.Pos η₀) b ε) :
    G.GeometryData η (G.Pos η) b ε := by
  refine ⟨?_, h.2⟩
  intro a ha
  cases a <;> first
    | exact False.elim ha
    | exact h.1 _ trivial

end ContinuousFlexibility.Analysis.N04RealizationGauge
