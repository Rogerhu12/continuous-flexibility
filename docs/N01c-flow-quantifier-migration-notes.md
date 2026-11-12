# N01c flow-quantifier migration notes

This note records the adaptations needed when the repaired N01c ordinary
flow contract is combined with N07b, N08, and the later N07a integration.
The migration covers eleven consumer modules: two from N07b, seven from N08,
and two additional consumers from N07a.
The actual merged-head CI and ancestry evidence are recorded in the final
report of [PR #23](https://github.com/Rogerhu12/continuous-flexibility/pull/23).
The construction-closure checkpoint is recorded in
[N01c-actual-construction-audit.md](N01c-actual-construction-audit.md).

## The retained quantifier order

The definition in
[`Statements/Nonlinear.lean`](../src/ContinuousFlexibility/Statements/Nonlinear.lean)
is

```lean
∀ k : ℕ, ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ...
```

The high seminorm order is `s + loss + parameterLoss`. The common base,
base loss, and state-neighborhood radius remain fixed. The additional
loss may depend on the parameter derivative order `k`; it is selected
before the spatial order `s`, component, evaluation point, state, or
directions. This is the manuscript's parameter-order loss `d_k`, as
documented in `N01c-loss-audit.md`.

A restriction proof fixes `k`, chooses its existing `parameterLoss`, and
reuses it for all `s`. If `loss ≤ loss'`, the high-index comparison is

```lean
s + loss + parameterLoss ≤ s + loss' + parameterLoss
```

Coefficient-family estimates retain their own existing quantifier order.
The additional flow loss is propagated only where the flow estimate is
used.

## N07b: two neighborhood restriction consumers

Both consumers reuse
[`ordinaryFlowBounds_restrict`](../src/ContinuousFlexibility/Analysis/N01cBoundsRestriction.lean).
That theorem restricts the same smooth directional jet to the smaller
open neighborhood, applies monotonicity of the one-high variation
weight, and keeps the selected parameter loss unchanged.

| Module | Adaptation |
| --- | --- |
| [`CoupledNeighborhoodRestriction.lean`](../src/ContinuousFlexibility/Analysis/CoupledNeighborhoodRestriction.lean) | The private flow restriction lemma accepts and returns `OrdinaryFlowFamilyTameBounds`, using the actual host-sampled material weight. The common coupled-neighborhood proof retains the new flow quantifier order. Main's N04 restriction and primitive-certificate transport remain part of the integration. |
| [`N06Neighborhood.lean`](../src/ContinuousFlexibility/Analysis/N06Neighborhood.lean) | `n06_flowJet_bounds_mono` states `∀ k, ∃ parameterLoss, ∀ s` in both premise and conclusion, with high order `s + loss + parameterLoss`. It delegates restriction to the generic theorem; `n06_N01Properties_mono` receives the resulting tower without changing its public conclusion. |

## N08: seven flow consumers

The N08 port was prepared against main
`bb96c26fa8f49615fd0bc6848b57922832088a2b`. The relevant calls include
direct flow-tower uses, extraction of directional smoothness, and an
indirect height-forcing chain. All seven files belong to the migration.
The later N07a merge changes `N08ParameterRestriction.lean`; its updated
port also preserves those new contracts, as described below. The other
six source files are unchanged between these two main snapshots.

| Module | Adaptation and propagation |
| --- | --- |
| [`N08ParameterRestriction.lean`](../src/ContinuousFlexibility/Analysis/N08ParameterRestriction.lean) | Both the private flow-tower alias and its restriction lemma retain `∀ k, ∃ parameterLoss, ∀ s`. The proof chooses the loss once for each `k` and uses `Nat.add_le_add_right (Nat.add_le_add_left hl s) parameterLoss` for a larger common loss. |
| [`N08OpticalControlType.lean`](../src/ContinuousFlexibility/Analysis/N08OpticalControlType.lean) | The helper extracting a `SmoothDirections` witness first chooses the loss at `k = 1`, then specializes the spatial order to `a + b`. Its public geometric conclusion needs the smoothness witness only. |
| [`N08FlowParameterBounds.lean`](../src/ContinuousFlexibility/Analysis/N08FlowParameterBounds.lean) | The first parameter derivative uses `hflow 1`, then its selected tower at spatial order zero. Every internal state seminorm uses `loss + parameterLoss`. The public Lipschitz statement is unchanged because its existential bound may depend on the fixed state. |
| [`N08ReferenceFlowVariation.lean`](../src/ContinuousFlexibility/Analysis/N08ReferenceFlowVariation.lean) | The flow-jet witness formerly extracted directly at orders `1, 0` is obtained by first choosing the order-one loss and then specializing to zero spatial derivatives. The variation statement remains unchanged. |
| [`N08RadialHeightForcing.lean`](../src/ContinuousFlexibility/Analysis/N08RadialHeightForcing.lean) | The forcing-integral estimate selects the loss at parameter order two. Its intermediate conclusion retains `∃ parameterLoss : ℕ` before the real constant and before every component and height direction, with high height seminorm `heightPairGrading S (loss + parameterLoss)`. |
| [`N08RadialForcingLowerBound.lean`](../src/ContinuousFlexibility/Analysis/N08RadialForcingLowerBound.lean) | The positive-slope bound carries the same existential loss and the same `loss + parameterLoss` height seminorm from the forcing-integral estimate. |
| [`N08PhysicalLabelTests.lean`](../src/ContinuousFlexibility/Analysis/N08PhysicalLabelTests.lean) | The test family is already uniformly bounded at every fixed seminorm order. The proof specializes that hypothesis to `loss + parameterLoss`, absorbs the resulting constant, and retains its original physical-label comparison conclusion. |

The two N08 intermediate theorem statements that acquire an additional
existential loss are `n08_radialHeight_forcing_integral_bound` and
`n08_radialHeight_positive_slope_bound`. Their consumer chain propagates
the same selected value all the way to the all-orders test-family bound.
The public `N08Statement` and the N08 blueprint conclusion remain
unchanged.

## N07a: material absorption and the updated restriction contracts

Main `c9b130b932d5c608befa1ae9c46bff36145880f2` adds two ordinary-flow
consumers. The material comparison is in
[`N07aCoefficientMaterial.lean`](../src/ContinuousFlexibility/Analysis/N07aCoefficientMaterial.lean).
Its private `n07aFlowVariationBound` now records the additional loss
explicitly, and `n07a_n01_flow_bound` extracts the entire spatial tower
after choosing that loss at a fixed parameter order.

The theorem `n07a_ordinaryFlowFamily_subpower` retains the same loss while
absorbing the material envelope power into an arbitrarily prescribed
positive power of `T.M`. Its output has the shape

```lean
(k : ℕ) :
  ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ...
```

The bound uses `oneHighVariationWeight` at
`s + loss + parameterLoss`. The proof selects the loss before `s`, then
performs the existing positive material-factor comparison for that
spatial order. The endpoint factor and height gain remain in the
estimate. The main snapshot has no callers of this helper, so its
corrected signature needs no further consumer changes. The public
`N07aStatement` remains unchanged.

The second consumer is
[`N07aConstructionRestriction.lean`](../src/ContinuousFlexibility/Analysis/N07aConstructionRestriction.lean).
Its `n07a_N01_restrict` proof directly reuses the already proved
`n06_N01Properties_mono` from its existing N06 import. That common
restriction theorem preserves the flow loss selected for each `k`
through every spatial order `s`, with high index
`s + loss + parameterLoss`. Reusing the theorem also avoids elaborating
the large `N01Properties` witness again in a duplicate proof. The public
restriction statement remains unchanged, and no heartbeat limit is
increased.

The same main merge extends N03 with
`ReturnCorrectionSpatialProperties` and carries both
`CanonicalGeometry.PrimitiveGeometryProperties` and
`CanonicalPrimitiveGeometry` through the N04 output. The updated versions
of `CoupledNeighborhoodRestriction.lean`, `N06Neighborhood.lean`, and
`N08ParameterRestriction.lean` retain these additions alongside the N01c
flow quantifiers. In particular, N03 restriction transports the new
spatial conjunct; restriction through N04 transports each primitive
certificate with its corresponding proved restriction theorem.

## Review and validation

The preparation review checked the seven source diffs against the stated
main commit, followed every changed intermediate declaration to its
consumer, and checked the patch against pristine source snapshots. A
second review checked the updated N07a integration files against
`c9b130b932d5c608befa1ae9c46bff36145880f2`, including both N07a flow
consumers and the three shared restriction contracts. The follow-up
whole-tree scan covered all 3,007 Lean files in that main snapshot and
included full and partial `N01Properties` destructuring, aliases,
long projections, and order-specialized flow calls. The ports add no
desired flow estimates as new hypotheses. They keep the additional loss
visible through restriction, material absorption, and the quantitative
forcing chain.

Final acceptance uses the complete latest-main merged build: both N07b
restriction consumers, all seven N08 files, and both N07a
consumers are compiled together. The public `N07aStatement` and
`N08Statement` are compared with main, and the project's full
blueprint/axiom audit remains enabled. PR #23 records the exact merged
commit and CI evidence after that verification.
