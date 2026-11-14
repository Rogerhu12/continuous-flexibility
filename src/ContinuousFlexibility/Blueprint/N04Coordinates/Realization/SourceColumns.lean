module

public import ContinuousFlexibility.Analysis.N04SourceColumnsAssembly

/-!
# N04Coordinates-Realization: source factors and columns

Given the interface, prove the current jets of the two source factors and of the left and nu column atoms.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1252-1265 and 1654-1677.
Task: docs/tasks/N04Realization-SourceColumns.md.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationSourceColumns : N04RealizationSourceColumnObligation :=
  n04SourceColumns_obligation

#print axioms N04RealizationSourceColumns

end ContinuousFlexibility.Blueprint
