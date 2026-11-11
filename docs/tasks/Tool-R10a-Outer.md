# Tool-R10a-Outer

## Problem

Lemmas 6.4 and 6.5: the inputs from the transition core and the deep tail, and the outer inverse built from two homogeneous solutions without division by a boundary value.

This is a tool task: it has no blueprint node. State the lemma in Lean exactly as the manuscript states it, in new modules under `src/ContinuousFlexibility/`, and prove it. It is used by: R10a.

## Completion standard

- Every assertion of the cited lemma is a Lean theorem with the same hypotheses and conclusions, in the generality the manuscript uses; nothing is weakened, specialised to an easier case or left as a hypothesis.
- No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- The modules are in the root import and CI is green.
- The pull request lists each assertion of the lemma with the name of its Lean theorem.

## Source

`paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 526–657.
