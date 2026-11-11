# R10a recovery checkpoint

The execution environment disconnected on 2026-11-11. These complete source candidates are preserved outside `src/` while their remaining dependency closure is reconstructed and compiled. They are not claims of completed regional proofs.

The implementation checkpoint `50fc03a97b12fec3bc7c5322fba138175231b614` passed full CI ([run 43039898089](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43039898089)). The task remains active. Geometry and Poisson are proved on the current branch; Regional is the open sub-statement. The newer main geometry contract will be integrated before completion.

These files include exact recovered snapshots and complete replacement candidates written against the same actual interfaces. Every candidate must be integrated into its original `src/ContinuousFlexibility/Radial/` path with all imports and checked by CI. No frozen hypothesis or conclusion may be weakened.

## Content inventory

| Module | Lines | Blob SHA1 |
|---|---:|---|
| FirstCentralGapInverse.lean | 155 | 4369fbad56e49f0d9b54339bafe550e5d9fe8414 |
| FixedCentralFirstInverse.lean | 89 | 40b1eb45c064f569ca6c02921d8337be6ee8328a |
| FixedCentralModelChart.lean | 240 | 43224a122684825ef9216bee435c8f15bc53d842 |
| FixedCentralModelColumnCost.lean | 134 | ba764d8fa097607f9ae97fce37065723705b46b2 |
| FixedCentralModelSmallError.lean | 151 | b45ee4824acfb86f045fc18c22d4213083b24fbf |
| InnerActualUnweightedHardyInverse.lean | 130 | f2d02a0261579b8d7d30deacbc74bb39327ad94e |
| InnerActualUnweightedInverse.lean | 122 | 4d8c5abe794db063ee10a8b277134df71593c1c4 |
| InnerGapHardyPoisson.lean | 76 | 325ad898049a610c35cc3b814d1bbfb126b8a55f |
| InnerRadialGapHardy.lean | 61 | b78d79753204dfc7d0f45f26f561bc55baeb1e01 |
| R10aRegionalConstruction.lean | 117 | f8be999e897c4d7895b09018ed72d4963c2f5e18 |
| RetainedLaterFrozenInverse.lean | 220 | e757d921670ac040bfce3cd4270694622d05e080 |
| RetainedMorseModelChart.lean | 145 | cd0826ebb15111d305d6e8e0e3370eec9d59f227 |
| RetainedMorseModelFamily.lean | 170 | 2d7c397a2297cdef818bfac011daa7f72b80d142 |
| ScaledMorseInnerGeometry.lean | 209 | 351a2a463f529650de05f2c933acba723c69fa31 |
| SelectedFirstInnerInverse.lean | 194 | 2287c94acb569045120f72012c2d28fb68c6ff1d |
| SelectedFirstRegionalData.lean | 312 | ed305a6dcf1389830f20a0aa89767b9adaddaa46 |
| SelectedLaterTerminalData.lean | 209 | 3f32e1fe0325445f70364fdd321983f55f571e89 |
| SelectedLaterTerminalRegional.lean | 122 | 8990e5ab08cfd64bf7f9f0e56d1e290152fa703e |
| SelectedNaturalRobinInverse.lean | 141 | b80ccd05e4e31c16555e65e275283357b75ac6fb |
| SelectedOuterGraphAssembly.lean | 112 | c5bfbebed45422f89d8aec9e0bac5ab847344c65 |
| SelectedOuterGraphUniqueness.lean | 113 | e3234e0f2224b395f51eb2aed34762192cd7eb57 |
| SelectedOuterNaturalUniqueness.lean | 159 | d84b383552aa25d2d9726a3b35e4ab7b8a5d24fb |
| SelectedOuterRealizations.lean | 109 | 79fd854c34fa746e1b3549b91a49ea07a31b3812 |
| SelectedOuterTestIntegrability.lean | 82 | 5d509956ab876e228fd5227d340b537304e575c8 |
| SelectedOuterTraceAssembly.lean | 107 | 735428d826cc86f81c58d089be2a14db27b62af2 |
| SelectedOuterWeakDuality.lean | 95 | 76a402b8d63b639b19547097194de5aef7e2d1c8 |
| SelectedOutwardRegionMeasure.lean | 161 | f724c79685f1a03b20a44da792c784155e57faf4 |
| SelectedPhysicalGreenKernel.lean | 189 | ef990c1398a8ee9ddaf2017a2dc4e5dd353300ec |
| SelectedPhysicalTailFactory.lean | 62 | 9cddf239725288cf0c4851bc512d31230a122a01 |
| SelectedRadialOuterInverse.lean | 145 | c7667b2fde1efcbe0e562be4207dd0e98aa7b959 |
| SelectedRetainedOuterRealizations.lean | 116 | 50ed2e2294ee703f6e1d6116134b60adaee2d741 |
| SelectedRetainedOuterSupply.lean | 60 | d4b37190ddf3bcbc21a18e9eb1ea2212a940a81b |
| SelectedRetainedRegionalInverse.lean | 151 | 79fe99d7397847321f845bd8818681ef63f5bb06 |
| SelectedScaledRobinInverse.lean | 82 | b76c2f6f7052594cc65b13ffb227d845abc7cd28 |
| SelectedTailCauchyUniqueness.lean | 171 | 918edd372efce6cf11ebdc80cdc03a195581ff4b |
| SelectedTailInverseRadius.lean | 166 | 199b88ef1e3095ac918e37aac7671b55ad45fa3c |
| SelectedTailRadiusWeakEquation.lean | 86 | a064b015fd751898e4bd1ec00ba7874c41cd08c5 |
| SelectedTailRegularResponse.lean | 186 | a7b0b8499f882e62437f758718865182b849d155 |
| SelectedTailWeakPairing.lean | 100 | 16cc7d42eab464c72eaeeaf4123ebe8b74ee93d3 |
| SelectedTerminalInnerSupply.lean | 37 | e031a4dd53f80c7a2b3a17d6887edd5487a99a1a |
| SelectedTerminalOuterSupply.lean | 28 | 9df867b9d1e5673f3d0a9d62d34fea1d1e5b5f58 |
| SelectedWholeGreenKernel.lean | 117 | 225986497c9a0675587bd307008e3fa9ae9dc749 |
| SelectedWholeWeakInverse.lean | 147 | eaf1fa9bd3d825cbd3534f61eb23e83339848b3a |
