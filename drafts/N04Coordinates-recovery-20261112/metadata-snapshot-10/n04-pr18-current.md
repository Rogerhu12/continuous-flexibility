## Goal and completion status

This PR proves the coordinate and source-conversion stage of Proposition 7.8. Its exact target remains:

```lean
theorem N04Coordinates (hN04b : N04bStatement) : N04cStatement
```

**N04Coordinates remains open; this PR remains draft.** The flow subnode is proved. The realization subnode still needs the uniform estimates and full primitive geometry on the same retained witnesses. No final canonical or primitive estimate has been added as an input, and no completion claim is based on static review alone.

| Subnode | Verified status |
|---|---|
| `N04CoordinatesFlowJets : N04FlowJetsTarget` | Proved. The axiom guard permits only `propext`, `Classical.choice`, and `Quot.sound`. |
| `N04CoordinatesRealization (hFlowJets : N04FlowJetsTarget) (hN04b : N04bStatement) : N04cStatement` | Open. The added `CanonicalPrimitiveGeometry` output is being proved on the same actual data. |
| Parent `N04Coordinates` | Assembles the two subnodes; its completion gate remains open until realization is proved and the exact parent axiom audit passes. |

## Current verification

Current line head is **`1128dfa9f256a358227759001b9f13fabc21f971`**, tree **`31f999251097e7e11fbd53becc7c5693077990fa`**. It contains current main **`bb96c26fa8f49615fd0bc6848b57922832088a2b`**. Main and its task rules are fetched before each push.

| Checkpoint | Result |
|---|---|
| [Complete CI128, run 43189072477](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43189072477), `9120cd663b87b5dd70ecafd208690adfd4cb54fb` | All libraries, generated root, default AxiomAudit and Blueprint passed: **7,162 build jobs; 3,178 / 3,180 source modules compiled; 35 / 42 Blueprint statements proved, 7 open**. The two source exclusions are existing repository exclusions. This is the latest complete green baseline. |
| [CI134, run 43197678492](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43197678492), `18d8867c` | **3,191 / 3,200** modules compiled. One downstream vector-jet rewrite needed the actual transport alias folded explicitly. Its independently reviewed proof-only repair is `62e0f8c6`. |
| [CI135, run 43198941463](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43198941463), `62e0f8c6` | **3,192 / 3,200** modules compiled. The transport module now compiles. Five diagnostics in `WholeComponentReferenceIdentity` reduce to equal-branch simplification and two incorrectly continued `exact` applications. |
| [CI136, run 43200026215](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43200026215), `3dbed841` | **3,193 / 3,200** modules compiled. Reference identity now compiles. Two downstream diagnostics in `WholePositiveTransportAssembly` need the reflected first projection and the exact logarithmic height function elaborated explicitly. |
| [CI137, run 43201549606](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43201549606), `1128dfa9` | **Attempt 2 building all libraries**. Attempt 1 was cancelled during pinned environment setup, before source compilation; the log does not identify the cancelling actor. The same job was rerun at 10:40:05 UTC and first checked after 10:45:05 UTC on 2026-11-12. The two proof-local normalizations have independent full-source reviews; public declarations, fixed widths, formulas, imports and options are unchanged. |

The active group contains 20 new transport, endpoint matching, height interpolation, reference identity and actual canonical-field modules. Its generated root has **3,146 imports / 3,200 source modules**. The current branch is **2,795 added / 0 deleted Lean lines** ahead of full-green CI128, below the 20,000-line limit. Failed CI129–136 logs are downloaded once and preserved with exact hashes; subsequent pushes repair the diagnosed modules and immediate matching patterns. A new feature group will be activated after this group passes complete CI.

The seven open Blueprint nodes in the latest complete build are **N01c, N02N03, N04b, N04Coordinates, N05, N06, N07a**.

## Mathematical work already verified by complete CI

The flow theorem begins with derivatives of the original periodic scalar field and its actual ODE. It derives mixed spatial flow jets with one common low state order and one fixed derivative loss. Its angular Grönwall exponent is controlled independently of high parameter derivatives.

The green dependency closure includes genuine periodic flows, joint parameter/time continuity, secant-based parameter derivatives, global circle inverses, return-map Jacobian bounds, regularized root flows, actual inverse-root derivatives, even/odd substitutions, ordinary extension jets, coordinate divergence and principal-density identities, boundary inverse germs, source pairing and material-weight absorption.

It also includes actual closed-negative transport, genuine positive-component adjacency, finite full-jet gluing, and the real radius-based component selector. The two negative halves use their actual moving physical domains. Source conversion applies on these state-dependent domains. One-endpoint cubic division costs three derivatives; the two-endpoint theorem costs six and gives the explicit bound `M / 36` after the actual numerator jets of orders 0, 1 and 2 are proved to vanish.

## Reviewed sources awaiting their own compilation

The next bounded group has **25 sources / 2,782 source lines**, with an audited 568-module project closure. It assembles all geometry fields, the retained negative cuts, both physical transmission identities, the actual coordinate operator and negative Airy principal density on one whole-component atlas. It also supplies the actual positive principal matching and interior cubic division. Every selected source and independent review has an exact hash binding. No static review is reported as compilation.

Further reviewed work follows the same construction:

- A state-dependent all-angle coefficient collar identifies the original stored N03 chart and height with the already chosen controlled root model. Its radius is used only for equality of germs.
- The actual N01 chosen-flow factory then gives all-angle root chart, height, inverse-height and Jacobian estimates on one common smaller neighborhood. The state-dependent identification radius does not enter these bounds. Relative inverse and product estimates now give the actual coordinate and height endpoint jets, and the derived finite bounds feed the same positive family without an endpoint-bound premise. The original typed atlas is retained when the neighborhood is restricted.
- Fixed-width Taylor and actual two-collar radial interpolation estimates keep high-order data linear and do not choose a new atlas or width for each requested derivative order. The angular lift is handled through its bounded displacement and positive-order jets. Actual all-order endpoint source estimates and a common finite-prefix envelope have been independently reviewed.
- The actual ambient positive construction uses a smooth, flat N01 coefficient-difference representative. Its cubic quotient has genuine germs equal to the divided field stored in the same atlas.
- The same radius selector gives C3 global relative transport and positive height from the actual finite root matching. Periodicity and reflection use only the true selected closed/open component domains.
- A true containing material cell is selected once for the positive component midpoint. Material comparison and decay do not assume that the entire positive component lies in one cell.

## Remaining mathematical obligations

The exact all-order potential and divided-coefficient estimates must still be proved with one fixed loss and one neighborhood, using the actual positive endpoint construction and the same material labels. The primitive certificate additionally needs its actual material-coordinate jets, global transport estimates and material-ratio estimates. Qualitative geometry alone is not being used as a numerical bound.

Absolute reference-source primitive factors require quantitative turning-slope information on the retained profile. Compact cosine and affine-cutoff tests have been made explicit with their full forcing and weighted source norms; they do not yet prove this bound. No alternative Morse reference has been substituted for the incoming Through03 witness, and no counterexample to the existential frozen statement is claimed.

The announced N01c repair was inspected read-only at its current branch head. Its named `N01PrimitiveGeometry` records a quantitative optical lower bound on the same profile, cells and material samples. That certificate is retained by its coefficient and speed intermediates but is discarded by its final `N01Statement` assembly. This does not supply a projection from current `Through03`. The same-witness propagation must be established explicitly before such a certificate is used here. Unmerged branch definitions have not been silently installed or assumed.

The earlier pre-primitive realization candidate and obsolete 519-target proposal are not activated and do not close the strengthened target. The integration scope has already exceeded the original node-size estimate; the two subnodes and this status explicitly record that larger scope.

## Source preservation and provenance

After the local executor reset on 2026-11-12, the pushed line was recovered from its actual Git history. Missing unpushed sources were reconstructed as new exact versions and received fresh reviews. No historical review or compilation receipt was fabricated for reconstructed bytes.

The [recovery branch](https://github.com/Rogerhu12/continuous-flexibility/tree/backup/N04Coordinates-recovery-20261112-0755), latest commit **`91ccaed07155aaa8fbda0d33c0a99686a2b92cc0`**, preserves the 10:38:37 UTC snapshot: **15 new Lean versions / 2,422 lines and a 758-file exact source index**. Its tree has **5,217 added Lean lines** from full-green CI128, including its actual line parent CI137. Unchanged and earlier versions resolve to their exact prior backup commits. Raw logs and patches retain their original bytes; proofs and reviews completed after this snapshot await the next preservation push.

This branch preserves uncompiled drafts outside the generated root; it is not a completion or merge request. The detailed earlier PR chronology is preserved in its metadata snapshots. The current line retains all verified main integrations, including the physical-domain and source-contract repairs.

## Final completion gate

Before this PR is marked ready: prove the exact realization and parent; verify their axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`; regenerate the root; integrate the current main; and pass every default library, AxiomAudit and Blueprint check on that exact final head.
