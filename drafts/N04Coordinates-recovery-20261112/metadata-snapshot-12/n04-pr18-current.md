## Current status — N04Coordinates remains open

The branch now contains current `main` **40242eae88c48c0d7edf55177c1bbb84798a10cb** and the N07a interface repair. Current head: **1ceec0b0a72a356c3ed08740438cbc84f0fffdec**; tree: **a11bbe227cca307c247ed8f8e27dbd3c309b18b4**. The full CI for this merge is pending. This PR remains a draft.

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
- The one-file transport repair at **1128dfa9f256a358227759001b9f13fabc21f971** was being checked by run **43201549606**, attempt 2. Attempt 1 was cancelled during environment setup without a Lean source build. Attempt 2 was still building at the last observation and has been superseded by this mandatory main/workflow merge; it is not recorded as green.
- The current-main merge was pushed at **2026-11-12 11:12:41 UTC**. Its first CI check is scheduled no earlier than **11:17:41 UTC**. Failed/cancelled logs are downloaded once and retained with hashes.

## Construction work and exact remaining obligations

The existing proof chain constructs genuine root charts and heights, actual moving negative domains, closed inverse germs, relative positive transport with fixed collars, finite principal-jet matching, and the same-atlas qualitative geometry/operator/source-pairing assembly. The held 25-module whole-atlas group and 19-module actual-family group have exact source/review manifests and remain outside the active source tree pending a successful validation gate.

Further independently reviewed, uncompiled leaves derive:

- Actual positive source jets and finite prefixes with a common low order and fixed loss; the chosen transport widths remain fixed before later derivative orders.
- Angular inverse and radial fiber pullback estimates with a single high state factor.
- Genuine planar inverse derivative bounds from forward derivatives and the explicit material cost of the actual Jacobian lower bound.
- Exact cancellation and material bounds for the two negative reference source multipliers containing `w′` and `w′/r`, evaluated at the actual current physical radius using a genuine component host.

The middle multiplier containing `w`, all required higher jets and uniform reference costs are still separate obligations. Qualitative collar choices are not treated as polynomial material bounds.

The strengthened transmission clause also makes a reference-gauge construction necessary: the identity reference used by the relative transport is not by itself the required raw chart/height first-jet matching. The fixed-reference formulas retain the same relative transport:
`F_z = P₀ ∘ σ_z`, `G_z = τ_z ∘ P₀⁻¹`, and `h_z = (h₀ / Q_z) ∘ σ_z`.
The positive reference functions must match the actual negative endpoint jets, and all new primitive obligations must be proved for that same resulting atlas. No final canonical estimate or transmission certificate is being inserted as a premise.

No formal counterexample to the complete existential target has been established. The current exact target and all new construction obligations remain in force.

## Recovery and source preservation

All **799** indexed files in snapshot 10 were restored from their recorded Git commit/path and verified byte-for-byte by SHA-256 after the local execution environment was replaced. The active branch was restored at the identical source tree before this main merge.

The latest backup is [snapshot 11, a578d9c0](https://github.com/Rogerhu12/continuous-flexibility/commit/a578d9c02b4eff7772950a5488f35a99cb970211), on `backup/N04Coordinates-recovery-20261112-0755`. It follows snapshot 10 **121a8cc85e0fae7ab1f20e849432bbfbe362f65a**, preserves the post-disconnection exact source and review objects, and records unreviewed/uncompiled versions explicitly. Earlier exact versions remain reachable through the backup history and source index.

Backup drafts are outside `src/`. Source preservation is not compilation evidence or a completion claim. No merge into main or ready-for-review transition has been made.
