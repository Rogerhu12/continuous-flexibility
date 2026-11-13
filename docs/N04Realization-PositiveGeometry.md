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

## Validation record

The merge of the updated lead (`a4733032`) exposed two rewrite failures in
`N04RealizationLeadReference`, where the replacement reference state is
definitionally the original reference state. The proof now states this
exact reference-atom equality before rewriting. This is part of the
current line's complete-CI responsibility under the revised rules.

The positive blueprint proof is still being assembled. Completion requires
its full proof, the strict axiom audit, and a successful complete CI run;
the interface changes and historical counterexample alone do not establish
completion.
