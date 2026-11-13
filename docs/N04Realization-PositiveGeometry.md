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
| `N04PositiveReferenceMaterialBounds` | Records the same chosen `Y,H`, all their forward/height/reciprocal jets, and all positive-order jets of `invFun Y` with one material sample per piece. | The reference producer already proves these estimates; the old wrapper discarded them. |
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

The positive blueprint now invokes the unconditional construction in
`N04PositiveGeometryProof.lean`. Its module checks the transitive axiom
set against `propext`, `Classical.choice`, and `Quot.sound`, and prints that
set for the CI log. Compilation fixes are being validated before recording
completion; the interface changes and historical counterexample alone do
not establish completion.
