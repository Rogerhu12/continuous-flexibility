# N04 realization: exact reference integration and same-witness completion

This is a read-only integration audit, preserved during the 2026-11-12 runtime interruption. It does not activate proof sources or claim compilation. Every source below remains under its original owner until the PR18 handoff.

## Exact baselines

- Own parent: `ea97b87a2522786b9e8058775f04f4a567562fc3`.
- Current main readback: `1ecee654ecfa9cf39b8d846dccbf593ec1c0f2ac`.
- Source branch readback: `794d5d0e3a0c7f6864660e89166fc58c6295cd70`, tree `49237cc2b902342c4a42b86d653fb00770d65d60`, pushed 20:46:21 UTC.
- Source recovery snapshot38: `0227745d7d0b759233e7714896f99493b29661d2`, frozen 20:48:10 UTC; SOURCE-INDEX blob `9d31bc34469e6788e5f9560fbbc7d5956fc5a4ba`.
- Source CI164 baseline: `c796387fb555392501c81f5b8bd834936251516c`, run 43285158817/job131416494593, reported complete success at20:28:42 UTC. Source coverage was4297/4302 project modules, with5 statements open on that source line. Source CI165 was awaiting validation in the PR18 description read at this audit.
- PR18's source head contains14 of the historical41 reference modules, selected by a separate1880-line current-contract proposal. It does not activate the other27, the complete auxiliary package, or the all-reference294/151 assembly. No ownership handoff was stated in the description read by this audit.

## Immutable manifests and counts

The adjacent JSON records every target path, original archive commit/path, blob, import and review binding.

| Selection | Modules | Lean source lines |
| --- | ---: | ---: |
| Historical reference-family group |41|4902|
| Complete auxiliary replacement |9|1085|
| Overlap: PhysicalSpacesAuxiliaryColumn and BufferedRadialAuxiliaryColumn |2|256|
| Union |48|5731|
| Source CI165 selected prefix |14|1880|
| Remaining union after that prefix |34|3851|

The old256+212+334+179 subtotal omitted the separately reviewed104-line BufferedAuxiliaryColumnWitness. The historical41 manifest is blob `0ae5d8a1d49a64c412183757910c6ff25507260c`; its original full-main gate remains unchanged. The new14-module proposal is blob `dfa280484b9f2153aad4cc13910d317e0508237f`, archived in snapshot38 as `quantitative/recovery/ReferenceFamilyPositivePrincipalPrefixC796Proposal.json`.

The full-reference294/151 assembly is separate from those41 modules and depends on later numerical reference packages. Its sources are unchanged from snapshot35:
- `acac62fd1903dd18733c1759927aca87ad7b045a:drafts/N04Coordinates-recovery-20261112/source-snapshot-35/root/reconstructed/ActualWholeReferenceNonAuxiliaryJets.lean`, blob `f92cac74d1a7d5f0f5906e27bb2d1aad8c37cdd5`.
- Same commit/directory, `ActualWholeReferenceJets.lean`, blob `46844fab38919d0d3808cbf39a16e63aae173e2e`.
- Full independent review owner selection is in snapshot36 commit `be31f3ade99ace57e0fc7760a89491bbf9cab771`, `source-snapshot-36/root/reconstructed/ActualWholeReferenceJetsReviewedManifest.json`.

## Dependency groups

1. Actual reference negative radial/endpoint fields feed actual positive endpoint interpolation and CanonicalPositiveReferenceFamily.
2. PositiveChartRangeGeometry plus the selected distinct-range WholePositiveReferenceGauge feed WholeReferenceGaugeAtlasData, Geometry, Operator and RelativeFields.
3. First-jet inversion/reconstruction, actual root/cut interfaces and matching feed WholeReferenceGaugeTransmission; the existing global transport adapter preserves the actual global relative map and height ratio.
4. Radial principal formulas and the same actual family feed qualitative ReferencePrincipal. Its uniform lower clause additionally uses the retained-profile principal material cost, described below.
5. Auxiliary replacement: PhysicalSpacesAuxiliaryColumn -> BufferedRadialAuxiliaryColumn -> BufferedAuxiliaryColumnWitness. CanonicalAuxiliaryNormalization -> CanonicalAuxiliaryDifferenceJets. CanonicalSinglePieceReferenceBounds plus the same retained support witness -> CanonicalAuxiliaryReferenceJets. CanonicalAuxiliaryAtomPreservation and these branches -> WholeReferenceGaugeAuxiliaryPackage.
6. The later positive15, positive scalar columns, negative geometry/principal/potential/scalar columns/regularity, static atoms and zero reference divided atoms feed ActualWholeReferenceNonAuxiliaryJets294, then auxiliary111 feeds ActualWholeReferenceJets151.

No independent fresh atlas or sample selection is needed by any of these interfaces. Material enlargement changes E0 and therefore its two ratio atoms; those ratios must use their dedicated enlarged-material static provider. Every other non-auxiliary atom is retained as a full-function equality.

## Required compatibility repairs against main1ece

The historical41 source selection has exactly two identified direct main-interface ports:
- ActualReferenceNegativeRadialFields line135: call `n04b_reference_actualTravelChart hN.1.1.2.2.1 hfield m hr theta`, removing the old positional hT/hS/hN arguments.
- Selected restricted WholeReferenceGaugeAtlasCutOperator102 line57: add `reference_flow := hfield.reference_flow` to its restricted N04bFieldRegularity record.

The analogous active record sites in N03RootEndpointPhysicalJets394 and WholeCanonicalAtlasRestrictedGeometry116 are already repaired on our branch.

Later quantitative source closure also includes old travel-call sites in ActualNegativeReferenceDerivativeSourceBounds138, ActualNegativeReferenceAiryCoordinate126 and ActualNegativeReferenceSourceSquares103, and a restricted field record in N03RootEndpointMaterialJets92-96. The stored main migration audit additionally records N04ActualTravelDifferenceAngularBounds133, outside the reference41 group.

Preserve our current main-compatible actual-travel/domain providers; do not replace them with the source line's older four-field contract. The complete migration matrix is snapshot38 `quantitative/recovery/Main1eceActualProviderConsumerReuseReadOnlyAudit.json`, blob `e7589c3732c96b25028cfc2a0a8434fe83a98798`. Its historical c796 selection is evidence, not authority to undo main integration.

## Existing exact sample-displacement provider

No new bridge is needed for the final material certificate.

`f98e15e4243d0d47a9d42fa40e64f60ed54691d3:drafts/N04Coordinates-recovery-20261112/source-snapshot-21/audit/reconstructed/WholeReferenceGaugeMaterialSamples.lean` has197 lines, blob `366a91fc3b296b373ac708fb6127a99e47e6ecea`.

Its theorem `n04WholeReferenceGauge_sample_endpointX` takes the original hT/hS/Through03/hfield/e0, supplied whole enumeration and positive cell map with midpoint membership, and arbitrary supplied same psi/chi/h0/tau/sigma/Q/N. With original A and final V defined from those inputs, it proves:

```lean
∃ B : ℝ, 0 ≤ B ∧ ∀ z m p,
  p ∈ physicalPieceOpen S V z m →
    p.1 ∈ Ioo D.a D.b ∧
    endpointX 1 (Statements.endpointDistance D (T.sample (V.cell m))) ≤
      endpointX 1 (Statements.endpointDistance D p.1) + B
```

This is before every state restriction. The negative helper is ActualNegativeMaterialSamples131 in that same commit/directory, using the actual typed half midpoint cell rather than C.cell. Positive midpoint membership is retained, including ambient-touching components. Imports are ActualNegativeMaterialSamples, PositiveComponentMaterialDecay and WholeReferenceGaugeAtlasData. The weaker height-decay corollary in that same source is not needed: our later exact-exponent material bridge already consumes the displacement itself.

## Two required same-family export corrections

These are signature proposals only; neither source file was edited by this audit.

### Retain the principal lower bound with the294 choice

The294 proof currently calls `n04Coordinates_actual_positive_reference_fifteenAtoms` once, obtaining C0/hC0/B/hB/hfinite and defining its literal degree-three Y/H. It then exports only Y/H and N04PositiveReferenceFamily, discarding those numerical/formula witnesses.

The existing exact `n04WholeReferenceGauge_actual_prescribed_referencePrincipal` in ActualPositiveReferencePrincipalAssembly134 consumes precisely that same C0/B/hfinite and literal Y/H, then proves ReferencePrincipal for the actual V whenever its construction-stage geometry is supplied. Its cost is proved by ActualPositiveReferencePrincipalMaterialCost194, not assumed.

Keep the current existential and outer e/tau/sigma/Q/N/href binders, but replace the final `∀ s, ...reference bounds...` payload by:

```lean
(∀ {b' : ℕ} {epsilon' : ℝ},
  0 < epsilon' →
  CanonicalGeometry Γ.reference S C V b' epsilon' →
  ReferencePrincipal (enlargedMaterialData T) S C V) ∧
(∀ s : ℕ, ...existing non-auxiliary reference bounds...)
```

Call the existing principal assembly at n=3 while C0/B/hfinite are still in scope. Transport from original T to enlargedMaterialData T using E0 monotonicity and the same positive B: the coefficient lower reciprocal only decreases. No new final estimate is introduced.

An equivalent valid export retains the exact C0/B/hfinite plus Y/H formula equalities; merely returning an unrelated existential principal witness is insufficient.

### Accept the later common neighborhood in151

The151 wrapper currently fixes A from the original hN/hfield but asks CanonicalGeometry V at exactly the original base/epsilon. Actual positive matching supplies geometry at a later b'/epsilon'. Reconstructing A from restricted hN would lose the explicit original-atlas identity.

After its e/tau/sigma/Q/buffer/href inputs, expose:
```lean
∀ (b' : ℕ) (epsilon' : ℝ),
  base ≤ b' → 0 < epsilon' → epsilon' ≤ epsilon →
  CanonicalGeometry Γ.reference S C V b' epsilon' →
  ReferenceRadial S C V →
  ...same auxiliary selection and payload at b'/epsilon'...
```

Keep A defined from the ORIGINAL hN/hfield. Restrict Through03 only for the auxiliary111 call and pass that original A explicitly; auxiliary111 accepts an arbitrary supplied K. Return the resulting Through03, geometry and zero auxiliary tower on b'/epsilon'. Include the principal continuation from294 for that same V; auxiliary field copies preserve the entire ReferencePrincipal predicate.

## Final same-witness wiring

N04RealizationSameWitnessCompletion already consumes exactly:
- Through03, A/B and hfield on one current neighborhood;
- ReferenceRadial, ReferencePrincipal, ReferenceJets, CurrentJets, AuxiliaryColumnGauge and TransmissionGeometry for one K;
- global E0 floor;
- same-atlas qualitative transport;
- the exact sample displacement above.

It then normalizes only the unused operator values, intersects the existing material/transport neighborhoods and returns all four final payloads for one normalized record. Global E0 floor is preserved by `le_enlargedMaterialData_E0` from our retained-start global floor.

Once held imports arrive, a small supplied-family gauge assembly is useful: consume the caller's chosen Y/H, its N04PositiveReferenceFamily, current tau/sigma/Q matching and reference identities, and the explicit original A. Apply the existing individual gauge geometry/operator/transmission/global-transport lemmas. Do not invoke CanonicalActualReferenceGeometry's two existential family factories after quantitative selection. Our existing N04RealizationWholeAtlas105 already handles the raw W geometry/transport stage.

Auxiliary replacement leaves the hfield, A/B/source pairing, transmission, global qualitative map and sample-displacement functions definitionally unchanged through its explicit field copies. If short public transport lemmas are needed for elaboration, they should expose those exact equalities rather than construct a second object.

No new Lean file, Git index/HEAD mutation, source activation or active-branch write was performed by this audit.
