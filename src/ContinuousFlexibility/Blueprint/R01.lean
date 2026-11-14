module

public import ContinuousFlexibility.Statements.Milestones
public import ContinuousFlexibility.Radial.Gauge

/-!
# Blueprint node R01

Source: `paper/flexible-surface-rewrite/05-flat-end-chain.tex` lines 252–268 (`eq:rad-eq-rm13`).

Task file: `docs/tasks/R01.md`. The statement is frozen. Proved.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R01 : R01Statement := by
  refine ⟨fun a r V hr hV hV₁ => ⟨?_, ?_⟩, fun a y w V hw hV hV₁ => ?_⟩
  · exact Radial.deriv_gaugeLift hr (hV (Real.log r))
  · exact Radial.deriv_deriv_gaugeLift hr hV hV₁
  · exact Radial.logGaugeEquation_source_identity hw hV hV₁

end ContinuousFlexibility.Blueprint
