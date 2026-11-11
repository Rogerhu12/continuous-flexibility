# ContinuousFlexibility collaboration

The target is the complete theorem in `paper/flexible-surface-rewrite/01-introduction.tex`,
not a conditional local theorem. Read `blueprint/README.md`, the relevant nodes in
`blueprint/manifest.json`, and `coordination/assignments.json` before choosing work.

Use Lean `leanprover/lean4:v4.35.0-rc3` with the locked mathlib revision. Do not
change the toolchain, dependency locks, or manuscript. The integration chat owns
public contracts, root imports, `AxiomAudit.lean`, blueprint generation, and final
completion claims. Other workers edit only their assigned files. Reconcile
`coordination/active-workers.json` before binding another chat to the same scope.

Existing compiled declarations are shared interfaces. Coordinate a proposed
change with integration before editing another worker's file. Shared-filesystem
workers deliver stable files; remote workers deliver complete files or patches.
Include exact theorem statements, manuscript correspondence, actual build output,
new imports, and remaining obligations in every handoff.

All mathematical proofs, including private helpers, must pass Lean without
`sorry`, `admit`, project axioms, `native_decide`, or `unsafe`. Use `ContDiff ℝ ∞`
for smoothness; the top order in `ℕ∞ω` means analytic. `PolarPoint = ℝ × ℝ` has
the max norm, so Euclidean metric identities use explicit coordinate pairings.
Do not assume a global real primitive of the polar connection on an annulus.

Run `lake build <module>` for owned modules. Integration adds every project module
to `ContinuousFlexibility.lean`, runs `lake build` with the owner-based axiom audit,
and updates/validates blueprint evidence. A passing blueprint or helper module
does not prove the final theorem or the existence of an input structure.

Use `LEAN_NUM_THREADS=4` for build processes in this shared Windows workspace.
Coordinate missing-dependency builds so that one worker owns each closure.
Track each running command by its owner's tool session through its terminal
exit status. Process inventories and unknown session IDs from another worker's
sandbox do not establish whether that owner's build has finished.
