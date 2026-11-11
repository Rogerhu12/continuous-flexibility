# Tool-AngularCommutator

## Problem

Lemma 8.4: regularity of an inverse from a commutator, on a Hilbert space with a nonnegative self-adjoint angular frequency operator, including the three-lines interpolation step.

This is a tool task: it has no blueprint node. State the lemma in Lean exactly as the manuscript states it, in new modules under `src/ContinuousFlexibility/`, and prove it. It is used by: N07a.

## Completion standard

- Every assertion of the cited lemma is a Lean theorem with the same hypotheses and conclusions, in the generality the manuscript uses; nothing is weakened, specialised to an easier case or left as a hypothesis.
- No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- The modules compile in CI (the root import is generated) and CI is green.
- The pull request lists each assertion of the lemma with the name of its Lean theorem.

## Source

`paper/flexible-surface-readable/08-stable-inverse.tex` lines 512–774.
