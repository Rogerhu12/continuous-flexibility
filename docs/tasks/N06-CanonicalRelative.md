# N06-CanonicalRelative

## Problem

Construct the actual canonical perturbed operator on one N05 graph and source space,
and prove a uniform relative norm bound linear in one fixed state seminorm.

Prove `ContinuousFlexibility.Blueprint.N06CanonicalRelative` in
`src/ContinuousFlexibility/Blueprint/N06/CanonicalRelative.lean`:

```lean
theorem N06CanonicalRelative (hN05 : N05Statement)
    (hgraph : N06WeakGraphStatement) : N06CanonicalRelativeStatement
```

The conclusion in `Statements/N06Parts.lean` retains every N05 property on the same
chosen construction and identifies the operator with `PerturbedCanonicalRelation`.
If canonical witnesses are reselected to obtain the needed state bounds and common
transmission domain, all cumulative properties must be preserved or reproved.

## Completion standard

- The exact theorem has a proof without `sorry`; its axiom audit shows only
  `propext`, `Classical.choice`, `Quot.sound`.
- Every used module compiles in CI and CI is green on the merge with current main.
- An additional hypothesis asserting controlled geometry, small operator norm,
  physical identification or a common graph does not complete the task.
- The relative operator is a bounded endomorphism of the chosen source level;
  a derivative-losing or material-losing replacement does not complete the task.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 319–489, with the actual
coordinate and source constructions in `07-fixed-geometry.tex` lines 992–1725.
