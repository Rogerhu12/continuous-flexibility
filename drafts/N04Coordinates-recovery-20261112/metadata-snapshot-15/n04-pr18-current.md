## Current status — N04Coordinates remains open

The branch contains current `main` **40242eae88c48c0d7edf55177c1bbb84798a10cb** and the N07a interface repair. Current head: **14d76e94d35b6e0aff823c24e9eb90c290c9f3d6**; tree: **faf90d203e5ee33e7f7a152f0f64429cc94c46c5**. This head was pushed at **2026-11-12 11:46:41 UTC** and its changed-module quick check has passed. The complete library build is still in progress (last checked **2026-11-12 12:04:06 UTC**, run **43212052593**, job **131161882002**). It removes only one redundant simplification identified by the completed previous run. This PR remains a draft.

The exact parent signature is unchanged:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

The parent assembles the two explicit subnodes. **FlowJets is proved**, with only `propext`, `Classical.choice`, and `Quot.sound`. **Realization remains open**, so the parent is not complete and its dependency audit is not yet restricted to the allowed axioms.

## Current-main migration

Main now requires the same chosen coordinates and neighborhood to carry both `CanonicalPrimitiveGeometry` and `CanonicalGeometry.PrimitiveGeometryProperties`. The latter retains reference radial gauge and principal positivity, the actual unit-piece spatial jets, genuine current-minus-reference parameter jets with the prescribed height gain, the radial supported auxiliary source, and actual forward transmission first jets.

This merge retains the new N03 `ReturnCorrectionSpatialProperties` clause under neighborhood restriction. A second mechanical change selects the smooth-tame component explicitly in `N03ErrorHomogeneousBounds`. Both changes were independently reviewed against the actual nine-part N03 definition; their theorem signatures, imports, options, objects and quantitative conclusions are unchanged. The Realization task and module documentation now explicitly cover the strengthened parent payload.

The root import was regenerated with `scripts/gen_root.py`: **3599 imports / 3656 source modules**. These are source-inventory numbers, not a claim that the new head has compiled. The branch now has main's layered cache and changed-module quick check with the five-minute per-file limit.

## Verification evidence

Last fully verified branch checkpoint:

- Head **9120cd663b87b5dd70ecafd208690adfd4cb54fb**, tree **f554bf96bcaedc6f8cc809ff404a4fdfe399733a**.
- [Full CI run 43189072477](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43189072477): **3178 / 3180 source modules compiled**, all default libraries, generated root, AxiomAudit and Blueprint status passed; **35 / 42 statements proved, 7 open** at that checkpoint.
- Open statements then: N01c, N02N03, N04b, N04Coordinates, N05, N06, N07a. Main has since integrated N07a; this PR will report fresh counts from the completed current-main run.
- The one-file transport repair at **1128dfa9f256a358227759001b9f13fabc21f971** had run **43201549606**, attempt 2 cancelled during the library build at **11:11:52 UTC**, before the main-merge push. The log does not identify the cancelling actor. Attempt 1 was cancelled during environment setup. Neither attempt is green. Attempt 2's raw olean counter includes extra files from a newer main cache and is not a count of this head's compiled source modules.
- The current-main merge at **1ceec0b0a72a356c3ed08740438cbc84f0fffdec** had [run 43207164285](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43207164285), which failed in the changed-module quick check after compiling **657 project modules**, with no per-file timeout. Its two errors were a redundant no-progress `dsimp` in `CanonicalWholePositiveTransport` and an unreduced `id p` before a rewrite in `WholePositiveChartGeometry`. Both have narrowly scoped independent source/delta reviews and are repaired by the current head.
- The failed run's raw cache counter was **3650 / 3656**, which is not a successful full-build inventory. The full libraries and Blueprint/AxiomAudit steps were skipped. The branch cache was saved successfully. Raw log SHA-256: **befc6f3b97e03970e3e6e2a6e641ab51e4efaae752d572b8e7704eab47a8f635**. Failed/cancelled logs are downloaded once and retained.

- [Run 43211219043](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43211219043), at **3a8671c128296b431a9a0d23ce6cec8702dd654c**, confirmed the two preceding repairs compiled. The quick check compiled **3 project modules** and then reported the same redundant `dsimp` pattern in the downstream `CanonicalWholePositiveRootMatching` at line 176. Its independently reviewed one-line deletion is the current head. Raw cache count **3653 / 3656**; full build and Blueprint/AxiomAudit were skipped, so these are not fresh full verification counts.

## Construction work and exact remaining obligations

The existing proof chain constructs genuine root charts and heights, actual moving negative domains, closed inverse germs, relative positive transport with fixed collars, finite principal-jet matching, and the same-atlas qualitative geometry/operator/source-pairing assembly. The held 25-module whole-atlas group remains outside the active source tree pending full current-head CI. A new 19-module actual-family proposal has been reconstructed from the retained exact source and independent reviews: **2794 source lines**, **792 project modules in its dependency closure**, and **40 public declarations with no collision**. It is gated on the complete 25-module group being installed and green; this new proposal does not recreate the lost historical proposal or an execution authority.

Further independently reviewed, uncompiled leaves derive:

- Actual positive source jets and finite prefixes with a common low order and fixed loss; the chosen transport widths remain fixed before later derivative orders.
- Angular inverse and radial fiber pullback estimates with a single high state factor.
- Genuine planar inverse derivative bounds from forward derivatives and the explicit material cost of the actual Jacobian lower bound.
- Exact cancellation and material bounds for the two negative reference source multipliers containing `w′` and `w′/r`, evaluated at the actual current physical radius using a genuine component host.

The middle multiplier containing `w`, all required higher jets and uniform reference costs are still separate obligations. Qualitative collar choices are not treated as polynomial material bounds.

The strengthened transmission clause also makes a reference-gauge construction necessary: the identity reference used by the relative transport is not by itself the required raw chart/height first-jet matching. The fixed-reference formulas retain the same relative transport:
`F_z = P₀ ∘ σ_z`, `G_z = τ_z ∘ P₀⁻¹`, and `h_z = (h₀ / Q_z) ∘ σ_z`.
The positive reference functions must match the actual negative endpoint jets, and all new primitive obligations must be proved for that same resulting atlas. The new same-record data, range geometry, operator/source pairing, relative-field identities and cut-jet transfer now have independent static reviews. The actual positive reference interpolation, root-circle matching and complete root/cut transmission are now connected. The **137-line actual reference-geometry assembly** has a full independent review: it selects one order-four reference family and one degree-three relative family, preserves the original negative atlas, and returns geometry, cut/operator/source pairing, reference radiality, transmission and the same global C3 relative transport on one smaller neighborhood. The actual positive principal formulas and the **318-line negative potential/all-piece qualitative principal chain** have full independent reviews as well. The uniform endpoint angular lower bound, all material jet towers and the actual supported auxiliary source remain unproved. These held files are not compilation evidence. No final canonical estimate or transmission certificate is being inserted as a premise.

No formal counterexample to the complete existential target has been established. The current exact target and all new construction obligations remain in force.

## Recovery and source preservation

All **799** indexed files in snapshot 10 were restored from their recorded Git commit/path and verified byte-for-byte by SHA-256 after the local execution environment was replaced. The active branch was restored at the identical source tree before this main merge.

The latest backup is [snapshot 14, 2391bb28](https://github.com/Rogerhu12/continuous-flexibility/commit/2391bb285a08c1ae79449b2e05595fed9c2a281f), on `backup/N04Coordinates-recovery-20261112-0755`. Its index records **1033** exact files; this snapshot adds **20 Lean sources / 2386 lines** outside `src`, together with current CI evidence and review manifests. It follows snapshot 13 **44b4443bdf6ad798d4b9631371234b8225f9718f**. Earlier exact versions remain reachable through the backup history and source index.

Backup drafts are outside `src/`. Source preservation is not compilation evidence or a completion claim. No merge into main or ready-for-review transition has been made.
