# Deferred N01c main-port changes

These files belong to the existing `line/N01c` work. They are not part of the
generated Lean root and are not a completed proof or a green CI result.

## Recorded sources

- Last successful N01c head: `e4e626d44ffa443a891c357c1f7fb64228d2417c`,
  [CI run 43170538811](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43170538811).
  It passed 6,061 jobs, compiled 2,089 / 2,091 modules (two excluded), and
  audited all N01c stages with only the three allowed axioms.
- Main inspected for this port: `ed02c473e9fa361a7188a17cffb9c1e5c19b9adc`.
- N07b source inspected: `b17b71d6d3b812df9bbcf8002c976496c1402964`.
- Current integration target, containing both R11a and N07b:
  `93f5906c14e93f96e5f731719c65c5330c16e9a5`.
- Required corrections: [PR #23, final review comment](https://github.com/Rogerhu12/continuous-flexibility/pull/23#issuecomment-6814332112).
- The corresponding failed integration log was read once, from
  [run 43146792596](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43146792596).

## Flow adapters on the N07b integration

The source-tree `CoupledNeighborhoodRestriction.lean` and
`N06Neighborhood.lean` now use the exact main `93f5906` implementations
with their flow helpers adapted to `ordinaryFlowBounds_restrict`.
They retain `forall k, exists parameterLoss, forall s` and the high
index `s + loss + parameterLoss` on the common neighborhood.
Main's N04 and Through05 primitive-geometry restrictions remain intact.

The two patch snapshots alongside this document both apply to the
unmodified files at `93f5906`, not to the already adapted source tree.
They contain only the required flow import/helper changes. Static patch
and import checks passed; this new atomic N07b migration awaits CI.

## Actual N01a construction

The exact remaining obligations are in
`docs/N01c-actual-construction-audit.md`. The current constructor drops the
containing-cell map by setting `C.cell := id`. Replacing that map also
requires the original bounded additive index shift. The separate uniform
pointwise optical lower bound is not supplied by the current upper-jet and
travel estimates.

The completed R11a factory now retains enough actual data to prepare both
certificates on the same `Γ.reference`. The new proof chain uses the
canonical central-plus-two-tail enumeration, overlap-based additive
index comparison, the uniform Morse optical envelope, radius dilation,
and the central simple-zero lower bound. Fixed-reference versions of
the R11a/R11b/R12 packaging preserve those certificates without changing
the public radial statements. N01a then uses the actual host cells and
the original affine material data and optical controls.

The new modules have undergone source and import review but await Lean
validation. They will enter `src/` in the earliest dependency-closed CI
batch. Local compilation was stopped under the repository time-budget
rule. `N01cMorseOpticalEnvelope.lean` here is the earlier draft snapshot;
the reviewed implementation is promoted with the new optical helpers.

## Main import batches

`main-ed02c47/` records import-closed batches from the old common ancestor
`2ec60e87ec46445329e1f491ce684b2e87621966` to the recorded main. The first
batch was imported in local commit `e475f9b`; it adds 17,978 Lean lines.
The other batches must wait until that batch passes CI. The N01a final
assembly is held until the primitive geometry is genuinely proved.

The manifests describe the historical plan, not the remaining current-main
work. The replacement plan has five dependency-closed batches targeting
`93f5906`, with reviewed N01c proof promotions: 18,347; 17,473; 17,584;
17,470; and 15,871 added Lean lines. The final merge additionally reserves
686 root-import lines and two status-script lines. Every batch must pass
CI before the next is applied, and the actual Git diff is checked again
before each push. The 20,000 limit includes Lean drafts.

## Publication and current CI

Terminal Git authentication was rejected for writes. The connected GitHub
app successfully published the two exact local source trees as commits
`07556de` and `33e9c69`, using a fast-forward update of the existing
`line/N01c`. Both returned tree SHAs were checked against local Git.

The first run stalled while fetching the final six Mathlib cache files.
The identical source tree was retried as `e4e626d`; its environment setup
and cache restoration succeeded, and
[CI run 43170538811](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43170538811)
passed the full build and axiom checks. The next reviewed integration
batch is now applied and awaits its own CI. PR #23 remains a draft until
a complete green build on the actual latest-main merge. No credential values are stored
in the repository or its Git configuration.
