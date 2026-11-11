import ContinuousFlexibility.Blueprint.N01c.Statements

/-!
# N01c: variations of the ordinary flows

Use the actual ODE and quantitative speed families to prove the weighted
ordinary-flow estimates at every parameter and spatial order on one common
neighbourhood.  The parameter loss may depend on the parameter order.
Source: readable §7, Lemmas `circle-flow`, `uniform-characteristic-flow-constants`
and `current-geometric-jets`, Steps 1 and 5.
Task: `docs/tasks/N01c-Flows.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N01cFlows (hSpeeds : N01SpeedStatement) : N01Statement := by
  sorry

end ContinuousFlexibility.Blueprint
