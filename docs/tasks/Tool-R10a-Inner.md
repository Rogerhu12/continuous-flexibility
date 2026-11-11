# Tool-R10a-Inner

## Problem

Lemma 6.3: the inner inverse on the finite inner domain at one frequency, from the cut models, the positive connectors and the interface matrix, with its two weighted bounds.

This is a tool task: it has no blueprint node. State the lemma in Lean exactly as the manuscript states it, in new modules under `src/ContinuousFlexibility/`, and prove it. It is used by: R10a.

## Completion standard

- Every assertion of the cited lemma is a Lean theorem with the same hypotheses and conclusions, in the generality the manuscript uses; nothing is weakened, specialised to an easier case or left as a hypothesis.
- No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- The modules are in the root import and CI is green.
- The pull request lists each assertion of the lemma with the name of its Lean theorem.

## Source

`paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 352–526.
