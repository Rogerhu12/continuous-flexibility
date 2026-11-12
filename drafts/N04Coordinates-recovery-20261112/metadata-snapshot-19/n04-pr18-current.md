## Current status — N04Coordinates remains open

Current head: **48cc52bba2227eb3d42e5792f5f0f163e1654ec7**; tree: **aa001f260b62a3daaceac488288b6b134f21f4bb**. The branch includes main through **8cebde34f6668c523facece3312949e9dbec3444** and its N07a interface repair. Main subsequently integrated N06 at **ebfd528f2dd0c690799187be45b7c5a5c4c6b26a**. That large upstream merge is queued immediately after this repair group passes complete CI, before activating any further modules. The nonlinear interfaces consumed by this group are unchanged; current rules were checked before pushing.

The last full green checkpoint is recorded below. CI144 compiled all three prior repairs plus the actual whole-atlas geometry and whole-positive cubic difference modules (**5 project modules**), then stopped at one alias-rewrite diagnostic in the dependent cut/operator assembly. This head, pushed at **2026-11-12 13:08:41 UTC**, presents that actual density triple with the same local atlas before rewriting its genuine chart-inverse identity. The complete public header, all other proof branches and imports are unchanged; the repair has independent full-source review. There are **2870 added Lean lines** since the last full green checkpoint. CI145 is pending; this PR remains a draft.

The exact parent signature is unchanged:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

The parent assembles the two explicit subnodes. **FlowJets is proved**, with only `propext`, `Classical.choice`, and `Quot.sound`. **Realization remains open**, so the parent is not complete.

## Latest verified full green checkpoint

- Head **14d76e94d35b6e0aff823c24e9eb90c290c9f3d6**, tree **faf90d203e5ee33e7f7a152f0f64429cc94c46c5**.
- [Full CI run 43212052593](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43212052593), job **131161882002**, completed successfully. The changed-module quick check, generated root, every default library including AxiomAudit, and Blueprint status all passed.
- **3654 / 3656 source modules compiled**, **7638 build jobs**, **36 / 42 statements proved, 6 open**. The two excluded modules remain outside the default build.
- Open statements: **N01c, N02N03, N04b, N04Coordinates, N05, N06**.
- Raw log SHA-256: **153926708ef88b67788300066a717216b163f4ed13b7cfb2bcbb749c9fd838fe**. Verified receipt SHA-256: **a9a5d0679db0e2f16b11f15e1667f57153a646f64663c0098a646df6c939e41b**.
- The earlier quick-check errors in `CanonicalWholePositiveTransport`, `WholePositiveChartGeometry`, and `CanonicalWholePositiveRootMatching` were repaired with independently reviewed, narrowly scoped proof-script changes. Their repairs are included in this successful complete build. Failed/cancelled logs are downloaded once and retained.

The new head has **3624 generated root imports / 3681 source modules**. Those are source-inventory numbers; the 25 newly activated modules and their precise repairs are awaiting complete CI. CI144's raw cached-object counter was **4188 / 3681**, because main's cache contains newly integrated N06 modules absent from this checkout. That counter is not a current-head compiled-module count or a successful full build. Its cached log has SHA-256 **78885c9e4a111f0aef05ca9438c014091b51c7b3d677ae61cf82e1d7633f99d7**. The branch uses main's layered caches and changed-module quick check with the five-minute per-file limit.

## Current-main migration and same-witness construction

Main requires the same coordinates and neighborhood to carry both `CanonicalPrimitiveGeometry` and `CanonicalGeometry.PrimitiveGeometryProperties`. The latter retains the actual radial reference gauge, reference principal positivity, unit-piece spatial jets, current-minus-reference parameter jets with the prescribed height gain, the supported radial auxiliary source, and forward transmission first jets.

The merge preserves N03's new `ReturnCorrectionSpatialProperties` under neighborhood restriction and explicitly selects the smooth-tame component in `N03ErrorHomogeneousBounds`. Both changes have independent reviews against the actual nine-part N03 definition. The Realization task and module documentation cover the strengthened parent payload.

The existing chain constructs true root charts and heights, moving negative domains and closed inverse germs, relative positive transport with fixed collars, finite principal-jet matching, and same-atlas geometry/operator/source pairing.

The next **19-module actual-family group**, reconstructed from exact retained sources and independent reviews, has **2794 source lines**, **792 project modules in its recorded closure**, and **40 public declarations without collisions in its checked provider tree**. All 25 prerequisites are installed. The immutable proposal is preserved; each subsequent provider repair is bound through its exact independent review. A fresh preflight and complete green CI on the N06 merge are required before its activation.

## Further reviewed work and remaining obligations

A fixed reference gauge preserves the actual relative transport through
`F_z = P₀ ∘ σ_z`, `G_z = τ_z ∘ P₀⁻¹`, and `h_z = (h₀ / Q_z) ∘ σ_z`.

The independently reviewed **137-line actual reference-geometry assembly** selects one order-four reference family and one degree-three relative family, preserves the original negative atlas, and returns geometry, cut/operator/source pairing, reference radiality, root/cut transmission, and the same global C3 transport on one smaller neighborhood. The **318-line negative potential/all-piece qualitative principal chain** is also independently reviewed.

New numerical interpolation leaves choose a displayed width from the actual finite radial Taylor data before constructing the reference coordinate and height. They provide the true range, full endpoint jets, global derivative bounds, and polynomial value/reciprocal bounds for that same height. The physical positive-principal lower-bound criterion uses those same functions and explicitly exposes the actual profile and numerical costs still needing uniform material estimates.

The actual drift material tower and both oriented root-axis towers are independently reviewed. They retain the same genuine host, material scale, low order and fixed loss, include zero-order jets, and charge no inverse qualitative model radius.

The **256-line auxiliary-column construction and replacement** is now independently reviewed: it constructs a genuine radial compactly supported source with the true physical integral equal to one, preserves the same N01–N03 and canonical geometry after replacing the column, and constructs its actual rank-one projection. A further **212-line reviewed proof** freezes its canonical source using the true inverse point, height and Jacobian on the normalization region, then proves all actual auxiliary difference jets vanish and constructs their zero `SmoothDirections` tower. This does not assert that other atoms have zero differences. The actual single-component support witness is retained. A further reviewed **334-line** reference estimate bounds this true auxiliary source on its actual compact image, proves it is zero on the other pieces, and obtains uniform sample-material bounds using the explicit enlarged material datum while preserving Through03 for the same objects. A new independently reviewed **179-line same-atlas assembly** now chooses the column and its support once and returns all of these auxiliary conclusions together for the same `V`, `S′` and explicit `T′`. Complete atom functions are preserved except the auxiliary column and the two explicitly changed E0 ratios; those ratio estimates remain separate.

The fixed radial-gauge principal transformation and finite-jet transfer are independently reviewed. They use the actual common inverse and the exact multipliers `H² Y′`, `H²`, and `H²/Y′`, preserving the finite matching order. The actual endpoint-jet transfer and global difference-germ extension are also independently reviewed. A subsequent actual cubic factorization is under review; its material numerator estimate and identification with the stored divided difference remain separate obligations. The raw optical lower used by the conditional root material chain is not currently a field of the retained `Through03` output; no projection of that missing certificate is assumed.

These additional leaves remain uncompiled outside the active source tree. The remaining realization work includes:

- deriving uniform sample-`E0` costs for the actual root and positive reference data, including the precise ambient-boundary scope;
- all required reference and current spatial/parameter jet towers and the prescribed height gain;
- quantitative potential and divided-coefficient estimates for the same final reference gauge;
- compilation and final integration of the reviewed same-atlas auxiliary package;
- the complete `CanonicalPrimitiveGeometry` certificate and exact final assembly.

Qualitative collars and per-component constants are not being treated as uniform polynomial material bounds. No final canonical estimate is inserted as a premise. No formal counterexample to the complete existential target has been established; the exact target remains in force.

## Source preservation

All 799 files in the earlier recovery snapshot were restored byte-for-byte from their recorded Git commit/path after the execution environment was replaced.

The latest backup is [snapshot 18, 456cd39a](https://github.com/Rogerhu12/continuous-flexibility/commit/456cd39af7215e75d7b1e8530ea749e7440ba57e), on `backup/N04Coordinates-recovery-20261112-0755`. Its index records **1232 exact files**. This snapshot adds **12 Lean sources / 1548 lines** outside `src`, together with CI143 evidence, the exact CI144 plan/payload, the reviewed N06 compatibility candidates and new review records. It follows snapshot 17 **62fd35116408c35e0e565addea82100f07fa19b2**; prior exact versions remain reachable through the backup history and source index.

Source preservation is not compilation evidence or completion. No merge into main or ready-for-review transition has been made.
