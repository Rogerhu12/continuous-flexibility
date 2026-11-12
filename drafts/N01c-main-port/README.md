# Historical N01c main-port snapshots

This directory preserves the earlier port plans and draft snapshots for the
existing `line/N01c` branch. The active implementations are under `src/`.
Nothing in this directory is imported by the generated Lean root, and its
older manifests are not instructions for applying a current-main merge.

## Completed construction work

The actual N01a construction now retains its reference, cells, normalized
optical controls, and genuine containing-cell map. The canonical component
enumeration proves the bounded additive index difference for that actual
map. The two Morse tails and the central component supply one uniform
pointwise optical lower bound, and fixed-reference inverse completion
retains both certificates in the resulting `RadialReference`.

The repaired N01a node and this construction passed the full build at
`1fedc057fbca5bda71bb1006eefd72f67f8aea2b`, in
[run 43183467191](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43183467191).
That checkpoint compiled **2,462 / 2,464 modules**, with **11 statements
open**, and enforced the allowed three axioms for N01a and all four N01c
stages. The complete construction and exact historical gaps are recorded in
[the construction audit](../../docs/N01c-actual-construction-audit.md).

## Flow ports and newer main revisions

The two N07b patch snapshots beside this document apply to the unmodified
files at `93f5906c14e93f96e5f731719c65c5330c16e9a5`. They are historical
patches, not patches to apply over the current source tree. The source
implementations preserve main's geometric payloads while using
`∀ k, ∃ parameterLoss, ∀ s` and high order `s + loss + parameterLoss`.

Later main revisions also introduced N08 and N07a consumers. Their active
ports and the propagation of each fixed parameter loss are described in
[the migration notes](../../docs/N01c-flow-quantifier-migration-notes.md).
No desired flow estimate is introduced as a new hypothesis.

## Validation and publication record

The original two local source trees were published through the connected
GitHub app as `07556de` and `33e9c69`, with their returned Git tree hashes
checked against the local trees. The original branch was fast-forwarded;
no replacement branch was created. The unchanged source retry `e4e626d`
passed [run 43170538811](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43170538811).

Subsequent main imports were split into dependency-closed groups and each
group passed CI before the next was applied. The limit is **20,000 added
Lean lines from the last actual green commit**, including Lean drafts;
the manifests in this directory describe older snapshots only.

Final acceptance requires a real merge of the current main, a complete
green build on the resulting head, and the strict N01c axiom gate. The exact
final merge parents, CI evidence, module count, open statement list, and
ready-for-review transition are recorded in
[PR #23](https://github.com/Rogerhu12/continuous-flexibility/pull/23).
