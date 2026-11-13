# N04Realization subnodes: common definitions and rules

`N04CoordinatesRealization` (`src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization.lean`)
is assembled from five subnodes in `Blueprint/N04Coordinates/Realization/`:
`PositiveGeometry`, `NegativeGeometry`, `PulledFields`, `SourceColumns`, `Principal`.
The assembly is `n04Realization_of_obligations` (`Analysis/N04RealizationLeadAssembly.lean`) with
`n04Realization_currentObligation_of_split` (`Analysis/N04RealizationLeadCurrentProof.lean`);
the optical, reference and sample obligations are proved. Realization is complete when all
five subnodes pass their axiom audits.

## Definitions

- `CurrentJetDataOn S T cell P b ε f f₀` (`Analysis/N04RealizationLeadCurrentData.lean`) is the
  per-family form of the frozen `CurrentJets` clause on the pieces `m` with `P m`: current
  `ContDiffOn ℝ ∞` and π-periodicity of `f z m` on `unitStrip`, a `SmoothDirections` tower in the
  sector parameter `z` of the spatial jets of `f z m - f₀ m`, a value bound and a tower bound with
  the cost `B * E0^B * H^(3/4)` at the sample of the piece. `CurrentJetDataOn.mono` restricts the
  neighborhood and the pieces; `CurrentJetDataOn.union` combines two families of pieces.
- `N04RealizationGauge` (`Analysis/N04RealizationLeadCurrentSplit.lean`) bundles the retained start
  `W`, its choices `X`, the piece enumeration `e`, the reference family `Y, H`, the positive transport
  family `τ, σ, Q` and the normalization region `N`. For an auxiliary column `η`, `G.V η` is the
  reference-gauged atlas after the replacement, `G.atomFamily η a` / `G.atomRef η a` are the current
  and reference atom families, `G.pulledPoint` is the inverse-chart point of a canonical unit point,
  and `G.pulled η F` is a physical field family pulled back by it.
- `G.Admissible b ε`: the reference family certificate, the identity at the reference state and the
  transport matching on the state neighborhood `(b, ε)`.
- `G.GeometryData η P b ε`: data for the eight geometry atoms (`atomIsGeometry`) and the pulled
  height on the pieces `P`. `G.FieldData η b ε`: data for the pulled physical coefficients `a, b, c`
  and the pulled left and `ν` columns on all pieces.

The positive geometry subnode chooses the positive family and the first neighborhood; every other
subnode may shrink the neighborhood, but must choose it before the auxiliary column `η`.

## Rules

- Do not change the statements or the definitions they use (`N04RealizationLeadCurrentSplit.lean`,
  `N04RealizationLeadCurrentData.lean`, `N04RealizationLeadAssembly.lean`). If a statement is false
  or unusable, say so in the pull request with the reason; the lead repairs it.
- Work on `line/N04Realization-<Subnode>`, cut from `line/N04Realization-lead`, and merge that
  branch when it moves.
- Heartbeats: in this tree `obtain`/`rcases` into goals with large `let`s or state-space gradings,
  and `rw`/`simp at` on hypotheses containing `pairGrading`, can exhaust the limit. Open existentials
  with `Exists.elim` or `.choose`/`.choose_spec`, and put grading arithmetic into private lemmas over
  an arbitrary graded space. `simpa using h` checks at reducible transparency; use `exact` when a
  `let` or definition must unfold.
- Older draft modules are indexed in `drafts/N04Coordinates-recovery-20261112/SOURCE-INDEX.json` at
  commit `0227745d` (`git show 0227745d:<path>`; each entry gives `stored_at.commit` and `.path`).

## Completion standard (each subnode)

- The theorem has exactly its stated statement and contains no `sorry`.
- Its axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Every used module compiles and the complete CI is green.
