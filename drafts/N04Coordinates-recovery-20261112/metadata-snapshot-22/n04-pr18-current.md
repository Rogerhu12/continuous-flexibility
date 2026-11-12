## Current status — N04Coordinates remains open

Current head: **2058ced3cbf364e7e3ec9980dc76a90785890554**; tree: **412f884b14caddd7586ab614ff4d092ef093849b**. The branch includes main through **c070da70d8df06e5345ff10f63aeff17207f257e**, including N06 and the latest cache-retention workflow changes. Current rules and frozen nonlinear interfaces were checked before pushing.

Complete **CI146 passed** on the preceding exact merged head. This new head, pushed at **2026-11-12 13:54:18 UTC**, installs the independently reviewed **19-module actual fixed whole-coordinate family**: **2794 source lines plus 19 generated imports**, all with exact provider-transition evidence. **CI147 failed** in the changed-module quick check on this exact tree ([run 43231774602](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43231774602)); the full build and AxiomAudit steps were skipped. The cached log identifies five source files needing explicit namespace/order/alias elaboration repairs, including one private endpoint proof heartbeat timeout. These repairs are in progress; the last complete green remains CI146. This PR remains a draft.

The exact parent signature is unchanged:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

The parent assembles the two explicit subnodes. **FlowJets is proved**, with only `propext`, `Classical.choice`, and `Quot.sound`. **Realization remains open**, so the parent is not complete.

## Latest verified full green checkpoint

- Head **03e526021c371413f03fc0ce052476b63e105361**, tree **efb21c64394350528d48b98e247b5036edaa4b46**.
- [Full CI run 43226404498](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43226404498), job **131210616189**, completed successfully at **2026-11-12 13:49:51 UTC**. The changed-module quick check, generated root, every default library including AxiomAudit, and Blueprint status all passed.
- **8174 build jobs**, **4189 / 4191 source modules compiled**, **4132 generated root imports**, **37 / 42 statements proved, 5 open**. The two excluded modules remain outside the default build.
- Open statements at that exact green head: **N01c, N02N03, N04b, N04Coordinates, N05**.
- Raw log SHA-256: **1f5f378ad2b6b892c6671687aaa4f819c4ff8d0a88e9a4092497bff61db2166e**. Verified receipt SHA-256: **816420cab434c28d2f5fa7e9236ac0d823801164587e033f41e3f6771f097483**.
- This successful build includes the N06 merge and all four independently reviewed compatibility resolutions. Failed/cancelled logs are downloaded once and retained.

The current head has **4151 generated root imports / 4210 project source modules** (**4214** Lean files across `src`). CI147 did not reach the full build; no complete-build claim applies to this head. The branch retains the layered caches, changed-module quick check and five-minute per-file limit. The latest workflow saves a new branch cache before deleting obsolete ones and preserves failed-line packed build artifacts.

## Current-main migration and same-witness construction

Main requires the same coordinates and neighborhood to carry both `CanonicalPrimitiveGeometry` and `CanonicalGeometry.PrimitiveGeometryProperties`. The latter retains the actual radial reference gauge, reference principal positivity, unit-piece spatial jets, current-minus-reference parameter jets with the prescribed height gain, the supported radial auxiliary source, and forward transmission first jets.

The merge preserves N03's new `ReturnCorrectionSpatialProperties` under neighborhood restriction and explicitly selects the smooth-tame component in `N03ErrorHomogeneousBounds`. Both changes have independent reviews against the actual nine-part N03 definition. The Realization task and module documentation cover the strengthened parent payload.

The existing chain constructs true root charts and heights, moving negative domains and closed inverse germs, relative positive transport with fixed collars, finite principal-jet matching, and same-atlas geometry/operator/source pairing.

The **19-module actual-family group** is now installed in CI147. Its immutable proposal records **2794 source lines**, **792 project modules in its closure**, and **40 public declarations**. Reviewed provider transitions preserve its exact authority and account for subsequent compatibility repairs.

The next **41-module reference-family group** remains held until CI147 is completely green. Its immutable proposal records **4902 source lines**, **865 project modules in its closure**, **105 public declarations**, and **34 unique independent reviews**. A fresh preflight against the exact CI147 head verifies all source/review hashes, all dependency resolutions and every provider transition, with **zero missing prerequisites and zero public-name collisions**. No compilation result is claimed for this held group.

## Further reviewed work and remaining obligations

A fixed reference gauge preserves the actual relative transport through
`F_z = P₀ ∘ σ_z`, `G_z = τ_z ∘ P₀⁻¹`, and `h_z = (h₀ / Q_z) ∘ σ_z`.

The independently reviewed **137-line actual reference-geometry assembly** selects one order-four reference family and one degree-three relative family, preserves the original negative atlas, and returns geometry, cut/operator/source pairing, reference radiality, root/cut transmission, and the same global C3 transport on one smaller neighborhood. The **318-line negative potential/all-piece qualitative principal chain** is also independently reviewed.

New numerical interpolation leaves choose a displayed width from the actual finite radial Taylor data before constructing the reference coordinate and height. They provide the true range, full endpoint jets, global derivative bounds, and polynomial value/reciprocal bounds for that same height. The physical positive-principal lower-bound criterion uses those same functions and explicitly exposes the actual profile and numerical costs still needing uniform material estimates.

The actual drift material tower and both oriented root-axis towers are independently reviewed. They retain the same genuine host, material scale, low order and fixed loss, include zero-order jets, and charge no inverse qualitative model radius.

The **256-line auxiliary-column construction and replacement** is now independently reviewed: it constructs a genuine radial compactly supported source with the true physical integral equal to one, preserves the same N01–N03 and canonical geometry after replacing the column, and constructs its actual rank-one projection. A further **212-line reviewed proof** freezes its canonical source using the true inverse point, height and Jacobian on the normalization region, then proves all actual auxiliary difference jets vanish and constructs their zero `SmoothDirections` tower. This does not assert that other atoms have zero differences. The actual single-component support witness is retained. A further reviewed **334-line** reference estimate bounds this true auxiliary source on its actual compact image, proves it is zero on the other pieces, and obtains uniform sample-material bounds using the explicit enlarged material datum while preserving Through03 for the same objects. A new independently reviewed **179-line same-atlas assembly** now chooses the column and its support once and returns all of these auxiliary conclusions together for the same `V`, `S′` and explicit `T′`. Complete atom functions are preserved except the auxiliary column and the two explicitly changed E0 ratios; those ratio estimates remain separate.

The fixed radial-gauge principal transformation and finite-jet transfer are independently reviewed. They use the actual common inverse and the exact multipliers `H² Y′`, `H²`, and `H²/Y′`, preserving the finite matching order. The actual endpoint-jet transfer and global difference-germ extension are also independently reviewed. The actual cubic factorization is now independently reviewed. It derives the genuine closed-unit-strip factorization and the six-extra-radial-derivative estimate from the same current/reference principal fields. A generic stored divided-field identification is also reviewed; the actual fixed-gauge adapter is independently reviewed. The material numerator estimate remains separate. The raw optical lower used by the conditional root material chain is not currently a field of the retained `Through03` output; no projection of that missing certificate is assumed.

The actual root even/odd extension tower, positive odd-coefficient value and reciprocal, and arbitrary real-power spatial tower now have complete independent reviews. They use the same chosen inverse flow, true root label, fixed sample scale and common loss without charging inverse localization radii. The same retained Morse witness also gives a reviewed positive-gap inverse-width bound at its actual midpoint cell. Six fixed material-ratio atoms have reviewed genuine zero current-minus-reference spatial and `SmoothDirections` towers. These facts do not supply the other atoms' state jets.

Further independently reviewed leaves now identify the actual N03 root unit data, derive its physical material jets, recover the true reference slope from unit principal density, and obtain finite endpoint material costs. They preserve the original negative atlas and charge no inverse qualitative localization radius. Actual retained-reference positive component classification and endpoint-to-midpoint sample transfer are being connected to the displayed positive interpolation width.

The same whole-reference gauge now has reviewed ordinary smoothness and periodicity for all twelve static atoms, together with genuine zero state-difference towers for the corresponding static geometry/material functions. Actual negative H/M ratio estimates retain their exact original half-interval sample; E0 ratio estimates are being derived from the actual envelope endpoint model. These spatial statements do not supply the nonzero state-dependent CurrentJets tower.

A constructive gateway is also being extracted from the exact N01c branch witness so that the required Morse/reference certificates belong to the same retained reference function. The current N01c parameter-loss contract and the older N02 consumer contract differ; the adapter and upstream validation remain explicit outstanding work. No incompatible contracts or open Blueprint statements are silently composed.

These additional leaves remain uncompiled outside the active source tree. The remaining realization work includes:

- deriving uniform sample-`E0` costs for the actual root and positive reference data, including the precise ambient-boundary scope;
- all required reference and current spatial/parameter jet towers and the prescribed height gain;
- quantitative potential and divided-coefficient estimates for the same final reference gauge;
- compilation and final integration of the reviewed same-atlas auxiliary package;
- the complete `CanonicalPrimitiveGeometry` certificate and exact final assembly.

Qualitative collars and per-component constants are not being treated as uniform polynomial material bounds. No final canonical estimate is inserted as a premise. No formal counterexample to the complete existential target has been established; the exact target remains in force.

## Source preservation

All 799 files in the earlier recovery snapshot were restored byte-for-byte from their recorded Git commit/path after the execution environment was replaced.

The latest backup is [snapshot 21, f98e15e4](https://github.com/Rogerhu12/continuous-flexibility/commit/f98e15e4243d0d47a9d42fa40e64f60ed54691d3), on `backup/N04Coordinates-recovery-20261112-0755`, pushed at **2026-11-12 13:44:10 UTC**. Its index records **1347 exact files** and this snapshot adds **14 Lean sources / 1959 lines** outside `src`, bringing the preserved uncompiled additions since the full-green140 recovery baseline to **3988 lines**. It also preserves the immutable next-group proposals and review records. Earlier exact source versions remain reachable through the backup parent history and immutable commit/path index. Later work will be included in the next preservation checkpoint; this backup does not mark held sources compiled.

Source preservation is not compilation evidence or completion. No merge into main or ready-for-review transition has been made.
