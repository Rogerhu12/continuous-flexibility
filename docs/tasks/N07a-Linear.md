# N07a-Linear

## Problem

Recover the normalized physical inverse from the same N06 Banach solution, prove uniqueness against every actual `HeightPair`, and prove the fixed-loss `LinearFamilyTame` estimate. The target is `ScalarLinearInverseProperties`, the first three clauses of the frozen scalar inverse target.

Prove `ContinuousFlexibility.Blueprint.N07aLinear` in `src/ContinuousFlexibility/Blueprint/N07a/Linear.lean`, with exactly the statement in that file.

## Completion standard

- The theorem has its stated type and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N07aLinear` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module used by the proof compiles in CI, and CI is green on the current-main merge.
- The actual N06 objects are retained. Inverse regularity, commutator estimates, source membership, solution smoothness, or tame bounds may not be added as construction-stage assumptions. A weaker or conditional target does not complete the task.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 637–790.
