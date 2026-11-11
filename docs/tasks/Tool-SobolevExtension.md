# Tool-SobolevExtension

## Problem

A linear extension operator from a half-line or an interval to the line that is bounded in every Sobolev norm (appendix on external inputs), and the Hadamard three-lines lemma in the form used by Lemma 8.4.

This is a tool task: it has no blueprint node. State the lemma in Lean exactly as the manuscript states it, in new modules under `src/ContinuousFlexibility/`, and prove it. It is used by: Tool-OneHighFactor, Tool-AngularCommutator.

## Completion standard

- Every assertion of the cited lemma is a Lean theorem with the same hypotheses and conclusions, in the generality the manuscript uses; nothing is weakened, specialised to an easier case or left as a hypothesis.
- No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.
- The modules compile in CI (the root import is generated) and CI is green.
- The pull request lists each assertion of the lemma with the name of its Lean theorem.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex` lines 237–354.
