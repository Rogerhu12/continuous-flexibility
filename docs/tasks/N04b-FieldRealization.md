# N04b-FieldRealization

## Problem

Realize a single cumulative N01--N03 construction whose actual corrected
coefficient fields are smooth on the physical annulus, periodic in the
angle, have positive radial coefficient, and are strictly hyperbolic on
every entire negative component. At the reference state, its actual stored
minus flow must equal the radial optical flow on each closed component.

Prove `ContinuousFlexibility.Blueprint.N04bFieldRealization` in
`src/ContinuousFlexibility/Blueprint/N04b/FieldRealization.lean`:

```lean
theorem N04bFieldRealization (hN04a : N04aStatement) :
    N04bFieldDataStatement
```

The real definitions are in
`src/ContinuousFlexibility/Analysis/N04bFieldRegularity.lean`.
All material, physical-space, nonlinear geometry, return equation and
corrected-operator witnesses may be chosen together. The conclusion
retains `NonlinearPropertiesThrough03`, including the genuine corrected
flow returns and the actual bilinear smooth tame source error.

No chart, canonical normal form or transmission certificate occurs in
this target. Regularity of the decoded source error cannot be substituted
for regularity of an arbitrary stored coefficient field.

## Completion standard

- The theorem has exactly this statement, contains no `sorry`, and its
  transitive axiom audit contains only `propext`, `Classical.choice`,
  `Quot.sound`.
- The coefficient functions are the functions actually used by the retained
  N03 operator and corrected characteristic flows. A merely conditional
  representative theorem does not close the task.
- Strict hyperbolicity is proved throughout each negative component,
  including outside the optical correction collars.
- The retained reference flow is proved equal to
  `θ - ∫ s in C.left m..r, Real.sqrt (-deriv D.w s / (s * D.w s))`
  throughout the closed component. This is a property of the explicitly
  constructed correction, before canonical coordinates are introduced.
- All modules compile and full CI is green after merging current main.

## Source

`paper/flexible-surface-readable/07-fixed-geometry.tex`, type completion
and optical residual completion preceding lines 992--1003.
