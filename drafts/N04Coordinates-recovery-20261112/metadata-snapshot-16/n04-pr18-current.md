## Current status — N04Coordinates remains open

Current head: **51f748cb71b876e4664d9d750240c7522d0cf92f**; tree: **44e29d2eafa37456221914df1e33e73f16ecba1a**. The branch includes current main **40242eae88c48c0d7edf55177c1bbb84798a10cb** and its N07a interface repair.

The previous head passed complete CI. This head, pushed at **2026-11-12 12:16:19 UTC**, activates **25 independently reviewed modules / 2782 source lines**, plus the 25 generated root imports. It assembles the whole canonical atlas, its domain and reference partitions, normalization and cuts, the actual operator/source pairing, and finite principal endpoint jets. There are **2807 added Lean lines** since the last full green checkpoint. The new CI result is pending; this PR remains a draft.

The exact parent signature is unchanged:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

The parent assembles the two explicit subnodes. **FlowJets is proved**, with only `propext`, `Classical.choice`, and `Quot.sound`. **Realization remains open**, so the parent is not complete.

## Verified current-main checkpoint

- Head **14d76e94d35b6e0aff823c24e9eb90c290c9f3d6**, tree **faf90d203e5ee33e7f7a152f0f64429cc94c46c5**.
- [Full CI run 43212052593](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43212052593), job **131161882002**, completed successfully. The changed-module quick check, generated root, every default library including AxiomAudit, and Blueprint status all passed.
- **3654 / 3656 source modules compiled**, **7638 build jobs**, **36 / 42 statements proved, 6 open**. The two excluded modules remain outside the default build.
- Open statements: **N01c, N02N03, N04b, N04Coordinates, N05, N06**.
- Raw log SHA-256: **153926708ef88b67788300066a717216b163f4ed13b7cfb2bcbb749c9fd838fe**. Verified receipt SHA-256: **a9a5d0679db0e2f16b11f15e1667f57153a646f64663c0098a646df6c939e41b**.
- The earlier quick-check errors in `CanonicalWholePositiveTransport`, `WholePositiveChartGeometry`, and `CanonicalWholePositiveRootMatching` were repaired with independently reviewed, narrowly scoped proof-script changes. Their repairs are included in this successful complete build. Failed/cancelled logs are downloaded once and retained.

The new head has **3624 generated root imports / 3681 source modules**. Those are source-inventory numbers; the 25 newly activated modules are awaiting CI. The branch uses main's layered caches and changed-module quick check with the five-minute per-file limit.

## Current-main migration and same-witness construction

Main requires the same coordinates and neighborhood to carry both `CanonicalPrimitiveGeometry` and `CanonicalGeometry.PrimitiveGeometryProperties`. The latter retains the actual radial reference gauge, reference principal positivity, unit-piece spatial jets, current-minus-reference parameter jets with the prescribed height gain, the supported radial auxiliary source, and forward transmission first jets.

The merge preserves N03's new `ReturnCorrectionSpatialProperties` under neighborhood restriction and explicitly selects the smooth-tame component in `N03ErrorHomogeneousBounds`. Both changes have independent reviews against the actual nine-part N03 definition. The Realization task and module documentation cover the strengthened parent payload.

The existing chain constructs true root charts and heights, moving negative domains and closed inverse germs, relative positive transport with fixed collars, finite principal-jet matching, and same-atlas geometry/operator/source pairing.

The next **19-module actual-family group**, reconstructed from exact retained sources and independent reviews, has **2794 source lines**, **792 project modules in its closure**, and **40 public declarations without collisions**. Its static preflight passes against this head, with all 25 prerequisites now installed. It stays outside `src` until the current head has complete green CI. This new proposal does not recreate the lost historical proposal or an execution authority.

## Further reviewed work and remaining obligations

A fixed reference gauge preserves the actual relative transport through
`F_z = P₀ ∘ σ_z`, `G_z = τ_z ∘ P₀⁻¹`, and `h_z = (h₀ / Q_z) ∘ σ_z`.

The independently reviewed **137-line actual reference-geometry assembly** selects one order-four reference family and one degree-three relative family, preserves the original negative atlas, and returns geometry, cut/operator/source pairing, reference radiality, root/cut transmission, and the same global C3 transport on one smaller neighborhood. The **318-line negative potential/all-piece qualitative principal chain** is also independently reviewed.

New numerical interpolation leaves choose a displayed width from the actual finite radial Taylor data before constructing the reference coordinate and height. They provide the true range, full endpoint jets, global derivative bounds, and polynomial value/reciprocal bounds for that same height. The physical positive-principal lower-bound criterion uses those same functions and explicitly exposes the actual profile and numerical costs still needing uniform material estimates.

The actual drift material tower and both oriented root-axis towers are independently reviewed. They retain the same genuine host, material scale, low order and fixed loss, include zero-order jets, and charge no inverse qualitative model radius.

These additional leaves remain uncompiled outside the active source tree. The remaining realization work includes:

- deriving uniform sample-`E0` costs for the actual root and positive reference data, including the precise ambient-boundary scope;
- all required reference and current spatial/parameter jet towers and the prescribed height gain;
- quantitative potential and divided-coefficient estimates for the same final reference gauge;
- the actual supported radial auxiliary source and preservation of N01–N03 for any replacement;
- the complete `CanonicalPrimitiveGeometry` certificate and exact final assembly.

Qualitative collars and per-component constants are not being treated as uniform polynomial material bounds. No final canonical estimate is inserted as a premise. No formal counterexample to the complete existential target has been established; the exact target remains in force.

## Source preservation

All 799 files in the earlier recovery snapshot were restored byte-for-byte from their recorded Git commit/path after the execution environment was replaced.

The latest backup is [snapshot 15, 71fd2c8b](https://github.com/Rogerhu12/continuous-flexibility/commit/71fd2c8ba445c4fa595f823339912f3d55744631), on `backup/N04Coordinates-recovery-20261112-0755`. Its index records **1068 exact files**. This snapshot adds **11 Lean sources / 1586 lines** outside `src`, together with current CI evidence, reviewed manifests and the next activation proposal. It follows snapshot 14 **2391bb285a08c1ae79449b2e05595fed9c2a281f**; prior exact versions remain reachable through the backup history and source index.

Source preservation is not compilation evidence or completion. No merge into main or ready-for-review transition has been made.
