# N04Realization subnodes: common part

## Problem

`N04CoordinatesRealization : N04cStatement`
(`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization.lean`) is derived from five
subnode theorems in `Blueprint/N04Coordinates/Realization/` (`PositiveGeometry`,
`NegativeGeometry`, `PulledFields`, `SourceColumns`, `Principal`) by
`n04Realization_of_obligations` and `n04Realization_currentObligation_of_split`. One line proves
one subnode.

Each line owns its subnode's statement. The present statements are the lead's first draft. When a
statement is false or unusable, the line writes the correct statement and changes the shared
definitions (`N04RealizationLeadCurrentData.lean`, `N04RealizationLeadCurrentSplit.lean`) and the
assembly with it, then proves it.

## Completion standard

- `N04CoordinatesRealization` keeps exactly the statement `N04cStatement` and is still derived from
  the five subnode theorems.
- The line's subnode theorem contains no `sorry`, and its axiom audit lists only `propext`,
  `Classical.choice` and `Quot.sound`.
- A refutation of a draft statement, or a conditional or relative version, does not finish the line.
- With `line/N04Realization-lead` merged, every module compiles and the complete CI is green. The
  other subnodes still compile, with `sorry` where still open.
- One pull request from `line/N04Realization-<Subnode>` into `line/N04Realization-lead`. It lists
  each changed statement or shared definition with the reason.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex`, lines 1211–1760 (coordinates on the
pieces, Lemma `uniform-characteristic-flow-constants`, Lemma `current-geometric-jets`).
