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
  cases a
  case chartRadial => exact h.1 .chartRadial trivial
  case chartAngleDefect => exact h.1 .chartAngleDefect trivial
  case inverseRadial => exact h.1 .inverseRadial trivial
  case inverseAngleDefect => exact h.1 .inverseAngleDefect trivial
  case height => exact h.1 .height trivial
  case heightInverse => exact h.1 .heightInverse trivial
  case jacobian => exact h.1 .jacobian trivial
  case jacobianInverse => exact h.1 .jacobianInverse trivial
  all_goals exact False.elim ha

end ContinuousFlexibility.Analysis.N04RealizationGauge
