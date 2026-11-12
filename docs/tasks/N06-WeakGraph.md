# N06-WeakGraph

## Problem

The positive-cylinder graph estimate for actual L² weak solutions, with no endpoint conditions.

Prove `ContinuousFlexibility.Blueprint.N06WeakGraph` in
`src/ContinuousFlexibility/Blueprint/N06/WeakGraph.lean`:

```lean
theorem N06WeakGraph : N06WeakGraphStatement
```

`Statements/N06Parts.lean` gives the exact distributional equation, coefficient bounds,
regularity conclusion, five weighted derivatives and frequency-independent constant.
Strong derivatives of the input solution cannot be added as hypotheses.

## Completion standard

- The exact theorem has a proof without `sorry`; its axiom audit shows only
  `propext`, `Classical.choice`, `Quot.sound`.
- Every used module compiles in CI and CI is green on the merge with current main.
- A smooth-solution estimate or a conditional density statement does not complete this task.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 256–318.
