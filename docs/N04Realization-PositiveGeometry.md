# N04Realization positive geometry

## Corrected interfaces

The task rules of `cd7d86b4` give each line ownership of its child statement.
The original universal supplied-buffer statement is false; its certified
counterexample remains in `N04PositiveGeometryObstruction.lean` and the
separate obstruction note. Proving that counterexample is not completion of
the corrected positive-geometry task.

The corrected construction keeps the same retained start, physical spaces,
midpoint samples, endpoint sources, canonical atoms, and `N04cStatement`.
It changes the following intermediate interfaces.

| Interface | Change | Reason |
| --- | --- | --- |
| `N04PositiveReferenceMaterialBounds` | Records the positive-order jets of the same chosen `Y` and `Function.invFun Y`, and all-order jets of `H` and its pointwise reciprocal, with one material sample per piece. | The reference producer already proves these estimates; the old wrapper discarded them. |
| `n04Coordinates_actual_whole_reference_nonAuxiliaryJets` | Returns that material certificate together with its existing family and all non-auxiliary reference jets. | The current construction must use the very family for which reference estimates are proved. |
| `N04RealizationReferenceObligation` and its proof | Preserve the material certificate in the existential output. | Avoids choosing an unrelated reference family in the positive node. |
| `N04RealizationPositiveGeometryObligation` | Takes the reference certificate and chooses the normalization buffer before its smaller neighborhood and actual transport. | Arbitrarily prescribed collars can defeat every uniform material bound. |
| `N04RealizationCurrentObligation` | Receives the same reference certificate and returns the selected buffer with the current atlas. | The final assembly must retain the buffer selected by the positive construction. |
| `CurrentJetDataOn` | Its directional towers, as well as its estimates and spatial regularity, are required on the selected pieces. | Positive and negative nodes each prove their own pieces; the proved union lemma supplies all pieces. |
| `n04Realization_currentObligation_of_split` | Carries the selected buffer through all five children and supplies the universal piece proof when collecting their towers. | Preserves the five-node derivation of the unchanged current-jet conclusion. |
| `n04Realization_of_obligations` | Uses the returned buffer and the original reference-family certificate. | Preserves one atlas throughout reference replacement and the final N04c witness. |

The old draft has the explicit name
`N04RealizationSuppliedBufferPositiveGeometryObligation`. Its negation does
not concern the corrected existential-buffer statement.

## Quantitative choices

`n04PositiveGeometry_exists_controlled_buffer` constructs a legal buffer
from the compact normalization support. The five consecutive gaps have
reciprocals bounded by one power of the actual enlarged material envelope
at the selected positive midpoint. The buffer and its cost are chosen
before every state, spatial order, or parameter order.

The endpoint and inverse modules use actual directional towers. In
particular, the finite coefficient inverse constructor proves smoothness
of the literal `Function.invFun` from the smooth forward family, positive
scalar derivative, and surjectivity. It then composes that finite
dimensional inverse with the original coefficient tower; no inverse
regularity hypothesis is substituted for the construction.

## Actual current-data construction

The endpoint traces come from the actual source maps and their root
contexts. The angular defect and the radial coefficients are composed
with the same endpoint inverse circle, and all their finite prefixes use
one low seminorm order chosen before the parameter and spatial orders.

`N04PositiveGeometryTransportSamplePrefix` records positive joint words
of the displayed transport and its inverse. It keeps the parameter
arity bound, the low and high seminorm boxes, the original component
sample, and one parameter-height factor. Boundary prefixes are aligned
by increasing their angular horizons before composition. This leaves
the normalized denominator unchanged; the additional shift pays for
turning boundary coefficients into plane fields.

The finite coefficient kernels, angular inverse, and moving-point
composition give this prefix for the actual `τ` and `σ`. Their constants
are collected into one material power before selecting a component or
state. No estimate for an independently chosen transport is assumed.

The physical height is formed from the same inverse transport and the
fixed reference height. The pulled height uses the identity between the
chosen forward and inverse transports. The coordinate construction uses
the reference chart and inverse chart, followed by the affine unit-cell
normalization. Its physical width factor is bounded by
`max 1 (D.b - D.a)` and enters only the finite constant.

Finally, the coordinate, physical-height, and pulled-height data are
restricted to one common neighborhood. The geometry collector produces
the remaining reciprocal and Jacobian atoms and transfers the result to
every auxiliary column. The final obligation retains the chosen buffer,
matching transports, and reference-state identities throughout.

## Validation record

The merge of the updated lead (`a4733032`) exposed two rewrite failures in
`N04RealizationLeadReference`, where the replacement reference state is
definitionally the original reference state. The proof now states this
exact reference-atom equality before rewriting. This is part of the
current line's complete-CI responsibility under the revised rules.

The positive blueprint invokes the proof term for the corrected obligation
in `N04PositiveGeometryProof.lean`. Its module checks the transitive axiom
set against `propext`, `Classical.choice`, and `Quot.sound`, and prints that
set for the CI log. Completion requires that check and the complete CI to
succeed on the integrated head; the interface changes and historical
counterexample alone do not establish completion. The final PR report
records the exact head, CI run, axiom output, compiled-module tally, and
open statements.

The 2026-11-14 integration at `7e7c344a` includes realization lead
`4facd3c1`, which supplies the proved NegativeChart and NegativeInverse
nodes. Its additions preserve the shared realization interfaces and the
original `N04cStatement` assembly. The local timings below predate that
lead merge and describe individual proof repairs, rather than the result
of the integrated build.

### CI performance repair, 2026-11-14

Run `43523267701` stopped `N04PositiveGeometrySourceSamplePrefix` after
305 seconds and reported a separate unfinished unit-vector inequality in
`N04PositiveGeometrySourceHeightWordBounds`. The inequality now uses
`norm_num [Prod.norm_def]` and passes its single-file check.

The source-prefix proof is split at its mathematical interfaces. The new
`N04PositiveGeometryBoundaryCompositionPrefixWordData` selects the four
finite-order composition constants and proves the plane-basis bound in
an abstract context. `N04PositiveGeometrySourceWordBounds` specializes
that bound to the actual source maps. `N04PositiveGeometrySourceSamplePrefix`
then supplies the material samples and seminorm windows. Explicit witness
projections and scalar envelope packing keep these steps separate during
elaboration; the source-prefix theorem statement is unchanged.

With the pinned Lean and Mathlib versions, the three files passed local
checks in approximately 7, 27, and 21 seconds respectively. Stage diagnostics
also confirmed why the intermediate single-declaration version was still
too large: it exhausted the default 200,000-heartbeat budget at the final
composition bound. Neither the heartbeat budget nor the CI file limit was
increased. The complete CI remains the completion gate.

The next compilation pass isolated the actual radial trace regularity
and the sector-unit seminorm estimate into small lemmas. Explicit maps
in the forward moving composition and explicit input word estimates in
the height composition remove ambiguous elaboration. The coefficient
jet proof now applies multilinear extensionality exactly once and takes
values of the coefficient identity with `congrArg`, rather than rewriting
the full actual-atlas context.

The physical unit-height prefix had another expensive existential
elimination, followed by a horizon rewrite and Boolean case split in its
large dependent context. Named witness projections, scalar equality
transport, a small pure-direction lemma, and separately typed physical
and affine bounds now keep those operations local. Its unchanged theorem
passed the pinned single-file check in 58 seconds. All these changes are
proof repairs; the parameter prefix, material sample, selected buffer,
reference certificate, and final theorem statements are preserved.

The four factor estimates use `N04PositiveGeometryActualFactorPrefixData`
to specialize the generic angular, radial, and inverse bounds to the actual
sector parameter space in separate declarations with explicit types.
The assembly also fixes its topological additive-group and continuous
scalar-action proof instances locally. This avoids repeatedly deriving
those same instances inside each saved-word bound; the four factor
conclusions and the order of all uniform choices are unchanged.

The two whole-component transports are then composed in an abstract
parameter space by `N04PositiveGeometryPlaneSavedTransportComposition`.
The actual-family adapter supplies its four factor bounds, the displayed
transport identities, and the closed-slab maps. The generic bound uses
the maximum of the unchanged factor cost and composition cost; the
existing sampled polynomial envelope absorbs both. This moves the
composition and pairing proof out of the repeated actual-atlas instance
search without changing the transport-prefix conclusion.

Run `43557895844` then stopped
`N04PositiveGeometryActualTransportSamplePrefix` after 310 seconds. The
index-bound proof now applies a pure natural-number horizon lemma instead
of rewriting the dependent actual-family context. The two normalized
root denominators are aligned with explicit `congrArg` equalities, and a
small abstract Boolean-selection lemma transfers the two transport bounds
to an arbitrary supplied tower. The public statement, material sample,
low and high seminorm windows, and order of the uniform choices remain
unchanged.
