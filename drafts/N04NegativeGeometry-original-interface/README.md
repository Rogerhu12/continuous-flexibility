# Historical audit of the original current-jet interface

These two modules were checked against the original, unguarded tower binder
at commit `3e23f7b3179f582b843c424779a2388a1a43f958` (CI run `43420024812`).
Their complete proof depends only on `propext`, `Classical.choice`, and
`Quot.sound`. They are retained here as the reason for the interface repair.

The active `CurrentJetDataOn` now indexes each tower by a proof of `P m`.
The historical negation is therefore intentionally not a theorem about the
repaired interface and is not part of the active build. The unchanged helper
lemmas for admissible gauges, height perturbations, and negative-piece
reductions remain in `Analysis/`.

This archive does not close the NegativeGeometry task. The current task is
the genuine negative-piece current-jet proof under the repaired definition,
with the final statement `N04CoordinatesRealization : N04cStatement` kept
unchanged and derived from the five subnodes.
