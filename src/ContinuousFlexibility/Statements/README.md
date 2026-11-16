# Statement layer

This directory holds the project's own Lean statements of the manuscript's milestones, written
for the first blueprint: 58 nodes (55 on the main chain, 3 side branches), indexed by
`Milestone.statement` in `Milestones.lean`. The current blueprint
(`src/ContinuousFlexibility/Blueprint/`) uses these definitions in several of its statements, and all
of its statements are proved (`docs/STATUS.md`).

## The main statement

`MainGeometry.lean` defines the project's statement of `thm:main`:

```lean
def MainStatement : Prop := Nonempty ClosedBending
```

`Contracts/SphereClosedBending.lean` proves it from a flat annular core, and
`src/Solution/FlexibleSphereSolution.lean` transports it to the Mathlib-only Challenge
`FlexibleSphere.ClosedBending` (`src/Challenge/FlexibleSphereChallenge.lean`), which is the
canonical statement. `ClosedBending` here states more than the Challenge: it also records the
Gaussian curvature, smoothness of the shape operator, positivity of area and volume, and an
ambient representative of the mean curvature. `C00Statement` and `MAINStatement` are aliases of
`MainStatement`, not separate theorems.

## Files

| File | Nodes or purpose |
| --- | --- |
| `Scalar.lean` | S01, S02; the scalar subgoals of S03–S05 |
| `ScalarWeighted.lean` | S03–S05 with the weighted spaces, tame estimates and flat endpoints |
| `Radial.lean`, `RadialTargets.lean` | R01–R12, X01: spectra, tails, collars, distribution graphs, inverses |
| `Analysis.lean` | W01–W03, H01–H03: weak derivative graphs, spaces and differentials |
| `Nonlinear.lean`, `NonlinearCompletion.lean` | N01–N12, X02: characteristics, fixed domains, coupled inverses, existence |
| `MainGeometry.lean` | C00, D01, D02, G01–G16, MAIN |
| `FiniteFourier.lean` | X03: the obstruction for finite Fourier squares |
| `Milestones.lean` | the index of the 58 nodes |
| `Audit.lean`, `MainGeometryAudit.lean` | axiom and `unsafe` audits of the declarations; checks that the 58 statements are closed `Prop`s |
| `manifest.json`, `window-evidence.json`, `check_statements.py` | manuscript locations and checks of the first workflow; CI does not use them |

The correspondence between the manuscript and these Lean statements is a matter of review, not
of names: the Challenge is the statement that was compared with `thm:main`.
