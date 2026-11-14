module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryProof
public import Lean.Util.CollectAxioms

/-!
# N04Coordinates-Realization: positive geometry

Choose one positive transport family with its matching on a smaller neighborhood and prove the current jets of the eight chart, inverse, height and Jacobian atoms and of the pulled height on positive pieces.

The statement is defined in
`src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean`.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 1237-1250 and 1679-1687 (Step 3 of the current geometric jets lemma).
Task: docs/tasks/N04Realization-PositiveGeometry.md.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Analysis

theorem N04RealizationPositiveGeometry : N04RealizationPositiveGeometryObligation :=
  n04Realization_positiveGeometry

end ContinuousFlexibility.Blueprint

open Lean in
run_cmd do
  let axioms ← collectAxioms
    ``ContinuousFlexibility.Blueprint.N04RealizationPositiveGeometry
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in N04RealizationPositiveGeometry"

#print axioms ContinuousFlexibility.Blueprint.N04RealizationPositiveGeometry
