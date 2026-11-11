# N07a-Smooth

## Problem

Prove smooth tame dependence of the same physical linear inverse by the actual forward family and Hamilton inverse-family theorem. A stronger low-order neighborhood is allowed; `G` and all underlying geometric data are retained.

Prove `ContinuousFlexibility.Blueprint.N07aSmooth` in `src/ContinuousFlexibility/Blueprint/N07a/Smooth.lean`, with exactly the statement in that file.

## Completion standard

- The theorem has its stated type and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N07aSmooth` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module used by the proof compiles in CI, and CI is green on the current-main merge.
- The actual N06 objects are retained. Inverse regularity, commutator estimates, source membership, solution smoothness, or tame bounds may not be added as construction-stage assumptions. A weaker or conditional target does not complete the task.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 790–815.
