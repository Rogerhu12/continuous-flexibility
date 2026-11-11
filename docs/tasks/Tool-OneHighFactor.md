# Tool-OneHighFactor

## Problem

Lemma 7.2 (estimates with one high factor: interpolation, product, composition with a smooth function, composition and inversion of circle diffeomorphisms) and Lemma 7.3 (flows on the circle).

This is a tool task: it has no blueprint node. State the lemma in Lean exactly as the manuscript states it, in new modules under `src/ContinuousFlexibility/`, and prove it. It is used by: Spaces, N01c, N04Coordinates.

## Completion standard

- Every assertion of the cited lemma is a Lean theorem with the same hypotheses and conclusions, in the generality the manuscript uses; nothing is weakened, specialised to an easier case or left as a hypothesis.
- No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- The modules are in the root import and CI is green.
- The pull request lists each assertion of the lemma with the name of its Lean theorem.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 237–399.
