# N04 PulledFields: quantitative reference data at the split interface

Date: 2026-11-13. Branch: `line/N04Realization-PulledFields`.

## Status of this audit

The current PulledFields split does not retain the quantitative reference
hypothesis which its parent already has. The available composition estimates
need that hypothesis. This note identifies the exact quantifier mismatch and
explains a static-middle reparametrization which is invisible to the supplied
current-difference data but changes the pulled-field derivative cost.

**This is an interface audit, not a Lean proof of the negation of
`N04RealizationPulledFieldObligation`.** The existing identities cited below
are proved in the source tree. The reparametrization and diagonal obstruction
are mathematical arguments which have not yet been assembled into a
counterexample satisfying every field of `N04RealizationStart`, every
admissibility condition, and the complete `GeometryData` premise in Lean.
Accordingly, this note does not mark the blueprint theorem complete or claim
that the main geometric theorem has been refuted.

No frozen statement is changed by this audit.

## 1. The exact clause and where the information is lost

In [N04RealizationLeadCurrentSplit.lean](../../src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean),
the frozen clause is:

```lean
def N04RealizationPulledFieldObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, G.GeometryData η (fun _ => True) b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ∀ η, G.FieldData η b' ε'
```

Here:

- `G` retains an arbitrary supplied positive reference family `Y, H`;
- `G.Admissible b ε` includes `N04PositiveReferenceFamily ... 4 G.Y G.H`,
  identity of the positive transports at the reference state, and
  `WholePositiveTransportMatching 3` on the state neighborhood;
- `G.GeometryData` supplies current spatial regularity, periodicity, and
  quantitative **differences from the reference** for eight geometry atoms
  and the pulled height;
- `G.FieldData` requires the analogous estimates for the physical
  coefficients `a, b, c` and the left and `ν` columns after pullback;
- `b'` and `ε'` are chosen before the auxiliary column `η`.

The parent statement in
[N04RealizationLeadAssembly.lean](../../src/ContinuousFlexibility/Analysis/N04RealizationLeadAssembly.lean)
already has the following order:

```lean
∃ newBase ε', ... ∧
  ∀ η,
    let S' := physicalSpacesReplaceAuxiliaryColumn W.S η
    let C' := geometryReplaceAuxiliaryColumn W.C η
    let L' := correctionReplaceAuxiliaryColumn W.L η
    let V' := canonicalReplaceAuxiliaryColumn
      (n04RealizationAtlas W X e Y H τ σ Q B.region) η
    ReferenceJets W.D W.U S' C' L' V' →
    ∀ a, a ≠ .auxiliaryColumn → ¬ atomIsStatic a → ...
```

Thus the parent is conditional on reference estimates for the **same atlas**.
The `SourceColumn` and `Principal` split conclusions retain this implication.
The `PositiveGeometry` and `PulledFields` split conclusions demand their data
before receiving it. In particular, adding a new conditional lemma about
pulled fields cannot prove the displayed frozen PulledFields statement.

The mismatch can also be seen in
[N04RealizationLeadCurrentProof.lean](../../src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentProof.lean):
`hfield G b2 ε2 hadm2 hgeo2` is called, and unconditional `hfd3` is extracted,
before the final `intro ... hrefJ` which receives the parent's reference
certificate.

## 2. A qualitative reference family has no material derivative bound

[CanonicalPositiveReferenceFamily.lean](../../src/ContinuousFlexibility/Analysis/CanonicalPositiveReferenceFamily.lean)
defines `N04PositiveReferenceFamily` by three requirements for each positive
component:

1. `PositiveChartRangeGeometry` for the reference chart, inverse, and height;
2. equality of coordinate endpoint jets through the supplied finite order;
3. equality of height endpoint jets through the same finite order.

The file explicitly describes this as qualitative existence without material
bounds on interpolation widths. Its `PositiveChartRangeGeometry` component,
defined in
[PositiveChartRangeGeometry.lean](../../src/ContinuousFlexibility/Analysis/PositiveChartRangeGeometry.lean),
contains global smoothness, inverse identities, positive Jacobian and height,
range conditions, periodicity, and reflection identities. It has no estimate
uniform over positive components.

Consequently, the order-four endpoint conditions do not bound interior
derivatives of either `Y i` or its inverse. Smoothness on each closed
component yields a finite bound for that component, but the conclusion
requires one `B` for all components, with only the prescribed material factor
`B * E0(sample)^B`. Componentwise compactness cannot produce that bound.

By contrast,
[ActualWholeReferenceNonAuxiliaryJets.lean](../../src/ContinuousFlexibility/Analysis/ActualWholeReferenceNonAuxiliaryJets.lean)
constructs a **particular** reference family, using prescribed Taylor widths,
and proves all-order uniform reference bounds for it. Its theorem has the
form `∃ Y H, N04PositiveReferenceFamily ... Y H ∧ quantitative_properties`.
It does not say that every `Y, H` satisfying the qualitative predicate enjoys
those properties. Replacing an arbitrary supplied `G.Y, G.H` by its witnesses
would change the atlas in the frozen conclusion.

## 3. Why the current geometry interface does not supply the missing bound

[N04RealizationLeadCurrentData.lean](../../src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentData.lean)
defines `CurrentJetDataOn` using mixed derivatives of

```lean
fun y => f z m y - f₀ m y
```

and smooth directional towers of that difference. There is no quantitative
bound on `f₀` itself. In particular, a static family can have arbitrarily
large spatial derivatives while its difference from its own reference is
identically zero.

This issue occurs in an actual region of the positive gauge construction.
The following are existing proved identities, not extra assumptions invented
for this audit:

- [WholePositiveReferenceGauge.lean](../../src/ContinuousFlexibility/Analysis/WholePositiveReferenceGauge.lean)
  defines the current chart as `ψ ∘ σ`, the inverse as `τ ∘ χ`, and proves
  `wholePositiveReferenceGaugeHeight_eq`, namely
  `h_z(p) = h₀(σ_z(p)) / Q_z(σ_z(p))`.
- [WholePositiveTransportAssembly.lean](../../src/ContinuousFlexibility/Analysis/WholePositiveTransportAssembly.lean)
  retains identity germs of the transport on the physical middle interval,
  through `WholePositiveTransportMatching.geometry`, and the constant-one
  height germ through `height_middle_germ`.
- `wholePositiveReferenceGauge_middle_germs` proves that the current chart,
  height, and inverse are equal to their fixed reference fields on the
  corresponding middle germs.
- `wholePositiveReferenceGauge_reference` proves that at the reference state
  they are exactly the supplied `ψ`, `χ`, and `h₀`.

For a fixed positive component, write its physical middle as `(c_i,d_i)`,
its radial reference chart as `Y_i`, and its inverse as `χ_i`. Choose a
smooth increasing diffeomorphism `Θ_i : ℝ → ℝ` which is the identity outside
a compact subinterval of `Y_i((c_i,d_i))`. Replace only the reference chart by

```text
Y_i' = Θ_i ∘ Y_i,       χ_i' = χ_i ∘ Θ_i⁻¹,
```

and keep the reference height, the transports, the normalization buffer, and
every physical field unchanged. This modification preserves the endpoint
germs, hence every finite endpoint jet. Its cylindrical lift preserves all
qualitative range and symmetry properties.

The resulting current inverse is
`G_z' = τ_z ∘ χ_i ∘ Θ_i⁻¹ = G_z ∘ Θ_i⁻¹`. On the support of the modification,
the transport is the identity and the old current-reference inverse
difference is zero. Off that support, `Θ_i⁻¹` is the identity. Therefore the
current-reference inverse difference is unchanged as a function of the
canonical unit coordinate.

The same argument applies to the forward chart and its Jacobian: on the
physical middle they are fixed to their references; outside the middle a
bijective transport which fixes the middle cannot carry a point into it.
The height and inverse-height differences are unchanged, and the pulled
height changes only in a region where it equals its reference. Angular
defects are unchanged because the reparametrization is radial. These
observations explain why all eight current geometry differences and the
pulled-height difference can remain unchanged while reference inverse
derivatives become arbitrarily large.

This paragraph describes the intended preservation argument. A complete
Lean preservation theorem for all nine families has not been added; it must
not be counted as a checked counterexample certificate.

## 4. What happens to a pulled physical coefficient

Let `F_z` be one of the physical coefficients and let
`ΔF_z(y) = F_z(G_z(y)) - F_ref(G_ref(y))`. The same change of reference chart
gives

```text
ΔF'_z = ΔF_z ∘ Θ_i⁻¹.
```

At a point where the radial derivative of `ΔF_z` is nonzero, the new first
canonical derivative is the old derivative divided by `Θ_i'`. The
qualitative reference conditions impose no positive lower bound on this
derivative in the middle. Since the conclusion is uniform over pieces,
the potentially problematic choice is a sequence of such modifications
over infinitely many pieces. A large derivative on just one fixed piece
would merely enlarge the allowed constant `B` and would not refute the
statement.

There is a concrete physical test for nonzero coefficient response. Keep
the profile `w` fixed and perturb the height by `q ψ(r)` with `ψ` smooth and
compactly supported in the physical middle. From `polarLinearA` in
[Scalar/Linearization.lean](../../src/ContinuousFlexibility/Scalar/Linearization.lean)
and the scalar discriminant definitions, the radial coefficient is locally

```math
a_q(r)=\bigl(w(r)+q\psi'(r)\bigr)
       \bigl(1-2q w(r)\psi'(r)-q^2\psi'(r)^2\bigr)^{-3/2}.
```

Thus

```math
\left.\partial_q a_q(r)\right|_{q=0}
  =(1+3w(r)^2)\psi'(r).
```

Choose the bump jet at an interior point `r_i` so that
`ψ'(r_i)=0` and `ψ''(r_i)=1`. Then the radial derivative of this response is
`1+3w(r_i)^2 > 0`. In sector coordinates the total height term is
`q * (U_ref + t ψ)`: the reference height field `U_ref` need not be zero.
Differentiating once in `q` and once in the genuine height direction `t`
removes the fixed `U_ref` term and gives the displayed response. Thus it is
detected by parameter order two at the reference point, without assuming
`stateU S C.referenceState = 0`.

The compact bump is a genuine element of the physical height space:
`exists_heightPair_of_compact_even_periodic` in
[CompactEvenHeightTests.lean](../../src/ContinuousFlexibility/Analysis/CompactEvenHeightTests.lean)
represents every smooth compactly radially supported even periodic field as
a `HeightPair` with zero endpoint constant. A radial bump satisfies those
symmetries. This avoids assuming that arbitrary pointwise physical tests
are automatically elements of the model.

These local calculations explain the obstruction; completing an exact
counterexample still requires a checked simultaneous reparametrization,
the full preservation theorem from the preceding section, infinitely many
appropriate pieces, and a diagonal estimate against every possible
`b'`, loss, and material constant. In particular, neighborhood shrinking
does not directly eliminate a positive-order directional derivative at
the reference point, but that observation alone is not the complete
quantified contradiction.

## 5. Existing composition tools and the premise they need

The strongest directly relevant existing tools are:

| Tool | What it gives | Additional input needed here |
| --- | --- | --- |
| `n04Realization_movingPoint_mixedRegularity` in [MovingPointMixedBounds](../../src/ContinuousFlexibility/Analysis/N04RealizationMovingPointMixedBounds.lean) | Genuine mixed regularity after evaluation at the moving point | A joint inverse-point tower and a map into the physical domain |
| `n04Realization_movingPoint_mixedHeight_bound` in [MovingPointHeightBounds](../../src/ContinuousFlexibility/Analysis/N04RealizationMovingPointHeightBounds.lean) | Mixed parameter/spatial bounds retaining one height factor at positive parameter order | Raw mixed-slot bounds for the complete inverse point, including its reference spatial derivatives |
| `n04Realization_positiveCoefficientFixedJointDirections` in [PositiveCoefficientJoint](../../src/ContinuousFlexibility/Analysis/N04RealizationPositiveCoefficientJoint.lean) | The actual corrected coefficient's joint tower on a positive physical interval | Positive-domain information; it does not bound the supplied reference inverse |
| `n04Realization_positive_inverse_material_weight` in [PositiveInverseSampleBounds](../../src/ContinuousFlexibility/Analysis/N04RealizationPositiveInverseSampleBounds.lean) | Material weights at a positive moving inverse point compared to the same sample | `CanonicalGeometry` and `ReferenceJets` for the same atlas |
| `n04Realization_mixedJointDirections` in [MixedJointDirections](../../src/ContinuousFlexibility/Analysis/N04RealizationMixedJointDirections.lean) | A joint tower from spatial/parameter mixed towers | Uniform seminorm control; joining towers alone does not supply material bounds |

The height-sensitive composition theorem has spatial cost
`t^(s + (offset+1)*k)`, so its parameter-order loss may depend on `k` while
remaining independent of `s`, as the frozen current-data definition permits.
This correct loss bookkeeping does not replace the missing bounds on the
zeroth-parameter-order reference inverse jets.

## 6. Minimal repair preserving the parent statement

A proposed two-file patch is available at
[N04PulledFields-reference-repair.patch](../../drafts/N04PulledFields-reference-repair.patch).
It changes only `N04RealizationLeadCurrentSplit.lean` and
`N04RealizationLeadCurrentProof.lean`; it leaves
`N04RealizationLeadAssembly.lean`, including the parent statement, unchanged.
`git apply --check` accepts the patch against the audited working tree.
That is a patch-context check, not a Lean compilation result. The patch has
not been applied to the frozen files.

A proposed repair, for the lead to decide, is to thread the parent's
same-atlas reference hypothesis through the split. An abbreviation such as

```lean
G.ReferenceData η :=
  ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
```

can make the change explicit. The PulledFields interface would then have
the form

```lean
∀ G b ε, G.Admissible b ε →
  (∀ η, G.ReferenceData η →
    G.GeometryData η (fun _ => True) b ε) →
  ∃ b' ε', b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
    ∀ η, G.ReferenceData η → G.FieldData η b' ε'
```

The positive geometry producer should likewise retain the reference
implication; the negative producer can remain stronger if its actual
fixed atlas supplies the required reference estimates independently.
SourceColumn and Principal must accept conditional geometry/field data,
and the current assembly must defer applying those conditions until it
receives `hrefJ` from the parent. Their conclusions already have the
reference implication.

The order `∃ b' ε', ... ∀ η, ReferenceData η → ...` is essential. Choosing
a new neighborhood after `η`, or after the numerical constants extracted
from a certificate for that `η`, would not match the parent. The
non-auxiliary objects and gradings are unchanged by replacing the
auxiliary column, so a correct proof should choose its loss/base and
radius from the common physical data and uniform composition construction,
then use the reference certificate for the same `η` to prove its bounds.
`ReferenceJets` itself has no neighborhood parameter and survives
neighborhood restriction without a new witness.

An alternative is to retain a quantitative certificate on the prescribed
`Y, H` in the gauge/reference-family interface and supply it from the
existing reference producer. That is a larger change. Merely choosing a
different reference family inside the PulledFields proof is not a repair
of the existing statement.

The proposed implication restores information already present in
`N04RealizationCurrentObligation`; it does not add an unproved premise to
the final geometric theorem. The full proof and axiom audit would still
be required after the lead repairs the split.
