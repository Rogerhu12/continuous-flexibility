module

public import ContinuousFlexibility.Analysis.N04PrincipalRealization

/-!
# N04Coordinates-Realization: principal, potential and divided coefficients

Given the interface, prove the current jets of the principal coefficients, the potential and the three divided coefficients.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1252-1308 and 1689-1698 (Step 4: division by d^3).
Task: docs/tasks/N04Realization-Principal.md.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationPrincipal : N04RealizationPrincipalObligation :=
  n04Principal_realization

#print axioms N04RealizationPrincipal

end ContinuousFlexibility.Blueprint
