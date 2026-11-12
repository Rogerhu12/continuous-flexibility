# Deferred N01c main-port changes

These files belong to the existing `line/N01c` work. They are not part of the
generated Lean root and are not a completed proof or a green CI result.

## Recorded sources

- Last successful N01c head: `7bc31f66b05ef96911654f4d9dda120c907c88e8`,
  [CI run 43128921355](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43128921355).
- Main inspected for this port: `ed02c473e9fa361a7188a17cffb9c1e5c19b9adc`.
- N07b source inspected: `b17b71d6d3b812df9bbcf8002c976496c1402964`.
- Required corrections: [PR #23, final review comment](https://github.com/Rogerhu12/continuous-flexibility/pull/23#issuecomment-6814332112).
- The corresponding failed integration log was read once, from
  [run 43146792596](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43146792596).

## Flow adapters

The source-tree `Analysis/CoupledNeighborhoodRestriction.lean` contains the
pre-N07b adaptation. It imports `N01cBoundsRestriction` and reuses
`ordinaryFlowBounds_restrict`, retaining `forall k, exists parameterLoss,
forall s` and the high index `s + loss + parameterLoss` on the common
neighborhood. Its other restrictions retain the current main interfaces.

`CoupledNeighborhoodRestriction-after-N07b.patch` is a patch against the
unmodified main file at the recorded main commit, **not** against the already
adapted source-tree copy. After the actual main merge, combine its flow hunk
with any upstream changes; its additional N04/Through05 hunks reuse
`n06_N04Properties_mono` and `n06_NonlinearPropertiesThrough05_mono` to retain
N07b's canonical primitive geometry.

`N06Neighborhood.patch` adapts N07b's abstract flow restriction to the same
quantifiers using `ordinaryFlowBounds_restrict`. It applies to the recorded
N07b source. Reconcile it with the actual main version after N07b lands.

The patch application, project import closure, absence of import cycles,
and the reused declarations' namespaces and argument orders were checked.
**Neither adapter has passed Lean compilation or CI in this session.**

## Actual N01a construction

The exact remaining obligations are in
`docs/N01c-actual-construction-audit.md`. The current constructor drops the
containing-cell map by setting `C.cell := id`. Replacing that map also
requires the original bounded additive index shift. The separate uniform
pointwise optical lower bound is not supplied by the current upper-jet and
travel estimates.

`N01cMorseOpticalEnvelope.lean` is an uncompiled proof draft for the actual
Morse realization. It converts the explicit optical lower coefficient to
one common negative power of `radialE`; it does not construct the missing
same-witness certificate or discharge N01a. Its existing prerequisite
exceeded the local compilation time budget, so local compilation was stopped
under the repository rules. Do not move the draft into `src/` without validation.

## Main import batches

`main-ed02c47/` records import-closed batches from the old common ancestor
`2ec60e87ec46445329e1f491ce684b2e87621966` to the recorded main. The first
batch was imported in local commit `e475f9b`; it adds 17,978 Lean lines.
The other batches must wait until that batch passes CI. The N01a final
assembly is held until the primitive geometry is genuinely proved.

The manifests describe the original complete plan; do not restore already
adapted files blindly. Regenerate or reconcile the remaining plan after
N07b lands. Keep the 20,000-added-Lean-lines limit from the latest green
commit, including drafts with a `.lean` suffix.

## Required remote access

The current task supplied a credential placeholder. The available
authentication could read the public PR but a push was rejected by GitHub
with HTTP 403 and `Permission to Rogerhu12/continuous-flexibility.git denied`.
No new commit was pushed and no new CI run was started. PR #23 remains a
draft. Resume pushing only with credentials authorized to write this
repository; never put credential values in a file, remote URL, or report.
