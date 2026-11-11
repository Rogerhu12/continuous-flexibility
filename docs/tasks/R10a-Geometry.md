# R10a-Geometry

## Problem

Choose one actual selected tail after the prescribed value of `Cstar` and an arbitrary lower bound on its starting index. Keep its canonical entries, actual Morse-chain witness, first-cone germs, smooth solutions, later join states and quantitative angle bounds. For every later choice of central model window, positive head length and positive retained-cone length, construct a common reference geometry with that same selected object and the prescribed fixed central border.

Prove `ContinuousFlexibility.Blueprint.R10aGeometry` in `src/ContinuousFlexibility/Blueprint/R10a/Geometry.lean`:

```lean
theorem R10aGeometry (hR06 : R06Statement) : R10aGeometrySupply
```

`R10aSelectedMetadata` records the actual selected construction. `R10aGeometrySupply` places the selected object before the quantifiers for the central window, head length and retained length. Its witnesses identify the final reference profile and height with the same retained pair, locate the central model window, and identify the actual reference column globally with the fixed column.

## Completion standard

- The theorem has exactly the displayed statement and contains no `sorry`.
- The supply uses the actual `SelectedTailData`, `SeedRetainedPair` and `ConnectedReferenceGeometry`. The selected object is unchanged when the later geometric parameters vary.
- The output includes the actual retained-cone and gap-slope data, and the physical profile, height, endpoints of the central patch and fixed central column identities.
- `#print axioms ContinuousFlexibility.Blueprint.R10aGeometry` shows only `propext`, `Classical.choice`, `Quot.sound`; all proof dependencies compile and CI is green.

## Source

`paper/flexible-surface-readable/06-global-reference-inverse.tex`, lines 352–776, together with the selected-tail construction in the preceding flat-end chain section.
