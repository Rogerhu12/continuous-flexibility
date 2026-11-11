# N04Root

## Problem

Even and odd parts of a smooth function under the substitution at a root, with fixed loss.

Prove `ContinuousFlexibility.Blueprint.N04Root` in `src/ContinuousFlexibility/Blueprint/N04Root.lean`:

```lean
theorem N04Root : RootCompositionTarget
```

## Completion standard

- `theorem N04Root` has exactly this statement and its proof contains no `sorry`; `#print axioms ContinuousFlexibility.Blueprint.N04Root` shows only `propext`, `Classical.choice`, `Quot.sound`.
- Every module the proof uses is in the root import and CI is green.
- A weaker, relative or conditional version does not complete the task. If the frozen statement is false or cannot be derived from its hypotheses, record that in `docs/STATUS.md` with the exact clause, and repair the statement together with `Blueprint/Assembly.lean`.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 1046–1211.
