# N07a-Angular

## Problem

Prove the weighted angular regularity and fixed-loss one-high estimate for the same `P.inverse` supplied by N06, on one stronger low-order neighborhood. The target is `N07aAngularProperties`; its weighted realizations must have exactly the original corrected source as their image under `V.forget`.

Prove `ContinuousFlexibility.Blueprint.N07aAngular` in `src/ContinuousFlexibility/Blueprint/N07a/Angular.lean`, with exactly the statement in that file.

## Completion standard

- The theorem has its stated type and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N07aAngular` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module used by the proof compiles in CI, and CI is green on the current-main merge.
- The actual N06 objects are retained. Inverse regularity, commutator estimates, source membership, solution smoothness, or tame bounds may not be added as construction-stage assumptions. A weaker or conditional target does not complete the task.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 489–635.
