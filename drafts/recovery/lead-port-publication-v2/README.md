# N04b compatibility ports for the N01c/N05 main contract (v2)

**Held source candidate; not compiled or applied.** This package contains one patch for **50 Analysis targets: 48 existing files and 2 new files**, totaling **+605/−383 Lean lines**. It retains the complete frozen 49-target package and appends the reviewed `N04bNegativeProfile` port (+2/−1), without changing any candidate bytes.

## Baseline and required order

The patch's exact before image is **`bcf08d9800e26ee6e95fd42a18e3c50ff7c08a6f`** (`integrate/n04b`). That commit contains main89, not the N01c/N05 contract used by these ports. **First perform the real merge of `43c5eea670bb872c0e0ae7c9cbe88097c6078fef` or a reviewed descendant into the integration branch; then apply this patch to the merged tree.** Do not apply it to the old contract or substitute copied main files for that merge.

For the locally inspected descendant `2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d`, the merge base with this baseline is `89e539ccf7e9c558467cf875f44dcff9490ce271`. Its main-side changes have **no path intersection with these 50 targets**; both new paths remain absent. Thus that main-side delta does not alter these patch preimages. Recheck if the integration tree or selected main advances; this is byte compatibility evidence, not a compile result.

From the repository root, after that real merge:

```sh
git merge-base --is-ancestor 43c5eea670bb872c0e0ae7c9cbe88097c6078fef HEAD
git apply --check drafts/recovery/lead-port-publication-v2/n04b-main43c5-contract-ports.patch
git apply drafts/recovery/lead-port-publication-v2/n04b-main43c5-contract-ports.patch
```

The commands are instructions for the lead; they have not been run against the repository by this package author. If a target was independently edited, reconcile it explicitly against the frozen target hashes below rather than force applying the patch. Full project CI and the existing endpoint axiom checks are still required after integration.

## Scope and preserved contract

The new ordinary-flow certificate chooses `parameterLoss` **after parameter order `k` and before every spatial order**. The ports preserve that choice and use `loss + parameterLoss k`; they do not assume a common loss or monotonicity in `k`. Fixed-order callers use their own order's loss, while the tower and endpoint estimates propagate the corresponding order. The local circle assembly permits an order-dependent neighbourhood and realizes the same scalar jets and actual circle family. Independent residual inputs and the original witness families remain intact.

The patch does not edit the three Blueprint endpoints `N04b`, `N04bFieldRealization`, or `N04bCanonicalConstruction`, their written headers, proofs, or axiom guards. It adds no endpoint premise. Supporting helper conclusions change where the new loss quantifier requires it. The root ports also reuse main's duplicate-declaration providers and adjust the physical-energy caller. No main sources, workflow, generated root, STATUS, or task documents are included.

Source review does not constitute Lean elaboration or a green CI attestation.

## Integrity

Patch: [`n04b-main43c5-contract-ports.patch`](n04b-main43c5-contract-ports.patch) — **153541 bytes**, SHA-256 **`f48f66340e651c323eb8f3db01a4f49ad2ba246f8a5347739f9adf5743aabfdb`**. The original 49-target patch is retained byte for byte as the prefix; its prior source, hash, and in-memory reconstruction checks remain applicable. The appended NegativeProfile hunk was independently reconstructed from its exact bcf before bytes and matches the frozen target SHA below. Only Git path headers and blob metadata were normalized. All 50 target hashes are listed below; actual patch application and compilation remain pending.

| Frozen group | Files | New | Added | Deleted |
|---|---:|---:|---:|---:|
| Root compatibility, including NegativeProfile | 5 | 0 | 14 | 54 |
| Fixed-order callers | 17 | 0 | 77 | 72 |
| Flow loss and endpoint propagation | 27 | 1 | 313 | 257 |
| Local circle assembly | 1 | 1 | 201 | 0 |

## Exact target SHA-256

All paths below are relative to `src/ContinuousFlexibility/Analysis/`. A **new** label identifies a path absent from the baseline.

| Target | State | SHA-256 after applying |
|---|---|---|
| `CircleLocalPositiveJetAssembly.lean` | **new** | `6e55cd9c6d34ab946796b318c8f1cfc522cfa145473d76426748fd8a2f5bca19` |
| `N01ActualCellMaterialOrder.lean` | existing | `436984f8e43cc72a9578d89600c66703ce304de334e2639ec4dde703c70b0f81` |
| `N01ControlFlowBounds.lean` | existing | `674a5f2d0414b15b5ff60c105b6493f215c43eff82a58fbe1cda7395edef825b` |
| `N01ControlIndexBound.lean` | existing | `b5d0a75bcf27c73439df46ff6fb6d08e5b156d5eaf29d12b4d9d9e20959bc684` |
| `N01ControlWeightConstraint.lean` | existing | `3581a809b144840d79d67a1507f291ce503e70162d29dda237dab3d9b9fbffdd` |
| `N01EndpointAngularJets.lean` | existing | `999e9310d1f6c076837f09995346a8174f6797dfb1b92adf302418f2a515d95b` |
| `N01EndpointCircleTower.lean` | existing | `c08627c12500251419e7c67cd7f6881b2e6036be249d883105765298a7fb1e02` |
| `N01EndpointHeightLineEnvelope.lean` | existing | `0eb7882e174a711c2dd0205027f8097f7b85c76d6d6ae43cc74ded9df9febc69` |
| `N01EndpointJetLocalGrowth.lean` | existing | `ba9ff4150bd83acaeaecb615cbd58dda688477fab9edcd3bf82a8143dfbc9733` |
| `N01EndpointOneHigh.lean` | existing | `e0e4f8ed2fa8e5f99545cc1c04c21d28acc5c70fc828263187b5f03094f47760` |
| `N01EndpointParameterTower.lean` | existing | `f1af876d0987f6ec59c246a8612011703a49acb2fd85415b9ff5371a4280998c` |
| `N01EndpointScalarCircleMember.lean` | existing | `8723cc1dfb401243a7501cf82efb2d7950fca1afb629bd7a12e054fb24e2c410` |
| `N01EndpointScalarHeightBounds.lean` | existing | `7afe9fb52e157e6e6143eb50bd0372f24550622d3b58fdd60296b354ef379a09` |
| `N01EndpointScalarJetGrowth.lean` | existing | `6483d8591b79807868a3db63a201df91106cba94cc08a7471c4947f3d604c412` |
| `N01EndpointScalarSplitNorm.lean` | existing | `529576ffcac4591b89d517ea30cc0226dd336af0dc405caf2967633fd1fdca9f` |
| `N01EndpointSmoothTame.lean` | existing | `80c1d63b655fd4fa1ee1dab48cf72c3740dbd3fb06b8bf20a313f305ebf79026` |
| `N01EndpointSplitEnergy.lean` | existing | `4faa6e7d0f9cb1865b7e77d212e465188c0865e5dcc1accb3828a750ded5c229` |
| `N01EndpointSplitNorm.lean` | existing | `070e867ec1c2350a17d09572c271522b299102e007f19992cff39253c870d7ff` |
| `N01EndpointStateCircleMember.lean` | existing | `4fa20bc3eaa9eb1bf6ae6bebafdf7218ec919b1763add9fbb57d6e8b248ab09e` |
| `N01EndpointStateEnvelope.lean` | existing | `a2dea4d1f155c38829a1554ed109d6cf022ac18015789a29820c7d3ceae43e48` |
| `N01EndpointStateIncrement.lean` | existing | `c97d51b21479891687d72e86519782244124124d77ea995731c28f1a6a4b23f3` |
| `N01EndpointStateJetGrowth.lean` | existing | `a4aea12ebbc0815a77362cde356e9ce3659260290743801bc505ec3a26670d51` |
| `N01EndpointWeightedJets.lean` | existing | `1a0163552e9a6b63a3940550fab1fcadb080736421a77a29f64f1d0a694749b6` |
| `N01EndpointZeroCircleMember.lean` | existing | `1a311ba9a58bf93ed1557bc3ccf80db939c3810467efae838058eea115a34136` |
| `N01EndpointZeroGrowth.lean` | existing | `3a65ee910f38dca6200c8a58d15e434480a9198f7e8a1a60066d85c282440ce4` |
| `N01FlowCircleUniformBounds.lean` | existing | `2ede43a0062e1475d3a26fc95b6f938d70577075415eee51cfb6d34ad6cbba27` |
| `N01FlowCollarJetBounds.lean` | existing | `fb0f4373d89051311bd1ce92f0c1046ee26fde5f4d665175a5e10165c2a797b5` |
| `N01FlowInverseJetBounds.lean` | existing | `e33d6b96e0857c1dfc6b1957b51bbe45089b72b07e8ccde68479c339e3106edc` |
| `N01FlowMixedParameterBound.lean` | existing | `a47a66bc82eb624226a6525968a5005bf10696ad6a662d8e389dbc2534b220cc` |
| `N01FlowMixedParameterTower.lean` | existing | `0ef715eedeab272778f41472a1e6a388ef2bedd9cb721a9149ac7767be4ec7c5` |
| `N01FlowParameterVariation.lean` | existing | `fda254d418bf89fed705ff8e7e8a0ba938073e35ff30118d444289d4786fe9c0` |
| `N01FlowScalarHeightBounds.lean` | existing | `ca9b60e638fd7d9e393981679f847beeb1f2bd7fb90ffc2c53b3cec200867c79` |
| `N01FlowSmallness.lean` | existing | `a879df53ee5e7599f0f1bb0699237d4664ef21c8da8033ee0cc0fdde6be23f0c` |
| `N01HeightResponseBound.lean` | existing | `39f238b54e0a18b5042b45c53b1648e9ea09a8b2075c3790b41c0f9f4ec16386` |
| `N01HeightTestWeightBridge.lean` | existing | `d8b5846936e62212dcbc90f5a7ffb552462dd46024437afe04679b259ea72dfc` |
| `N01HeightWeightConstraint.lean` | existing | `897b6cf3ccb743c0bac43573186bc67d60eb49aebfd3eef63b7f04fd8810cd52` |
| `N01NeighborhoodRestriction.lean` | existing | `3d4e965dff6150893fc90acfaddc9d89067c3421e41be21ac5a00654d655f805` |
| `N01OpticalCollarJetBounds.lean` | existing | `adc96f07ffe24e8ea5fa9f9211448915c6943a15eac94950a67374d5e316a3de` |
| `N01OrdinaryFlowLoss.lean` | **new** | `ffc22e1ef24bf12b8b9ead110277f3cc024cdc063647888e166a6e41c1708946` |
| `N01SectorFlowTower.lean` | existing | `eb26deb12403df97c1540bf4202363d086ca585fe34511098463a416050bb712` |
| `N03SourceFromCoefficientJets.lean` | existing | `5aae08ca1875c767643c568b0c37f9f94251c828453db8ce6906c447d648356c` |
| `N04bNegativeProfile.lean` | existing | `3aec80a153f446a261f198604f61e583f972c8c528d0fe86a57d34f2161f91d1` |
| `N04bSingletonType.lean` | existing | `ef362d90e09400526828fd85374a05510ed0845de56fb6112679e9e0e67be2a7` |
| `N04bStateProfileType.lean` | existing | `283c6d35d665b6168a0010701d26830a299d948fc21b5a4bad9be3c7f13d7347` |
| `PhysicalGradeEnergy.lean` | existing | `01166c23cf07b6c2d0ab9aa112b50ceef4ec139e773f85ae68487b0ca65826bb` |
| `PhysicalJetLinearity.lean` | existing | `5bffdc94f6e2810051395fcb2728819f9592dbd56f21695ad5da1ba16c5ce856` |
| `ReturnCorrectionBufferedCollars.lean` | existing | `c7ba7814a5ac0608ca8862cd3f425391095eea4fce507ef0b6f883e520a8b56b` |
| `ReturnCorrectionSmallness.lean` | existing | `3b4d56e5331a82354d2e4b73b5343e6d3666a700c2a525fafe881ac87dd6c829` |
| `ReturnCorrectionSpeedGap.lean` | existing | `88a21db11d91a771aec0b2fb993c204411661b3b608b21fcd12658bb0909b05b` |
| `ReturnCorrectionVelocityBounds.lean` | existing | `c125a572d4b6afc53686865b414c6c0c8bc989853c7c8092e93746ef672d0ff3` |
