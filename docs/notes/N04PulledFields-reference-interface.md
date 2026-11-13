# N04 PulledFields: quantitative reference data at the split interface

Date: 2026-11-13. Branch: `line/N04Realization-PulledFields`.

## Status of this audit

**Update after the task-rule revision `cd7d86b4`:** the line now owns its
statement and the necessary shared assembly changes. The reference-preserving
repair described in section 6 is applied to `N04RealizationLeadCurrentSplit`
and `N04RealizationLeadCurrentProof`; section 9 records the exact changes.
The historical audit below concerns the original draft. At `54bf9d13`, the
actual PulledFields blueprint placeholder has been replaced by the complete
assembled proof. Section 10 records that construction. Current compiler,
target-axiom-audit, and full-CI results are maintained in
[pull request #45](https://github.com/Rogerhu12/continuous-flexibility/pull/45).

The original PulledFields split did not retain the quantitative reference
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

The original audit did not change a statement. The authorized implementation
update is recorded separately below.

## 1. The exact clause and where the information is lost

In [N04RealizationLeadCurrentSplit.lean](../../src/ContinuousFlexibility/Analysis/N04RealizationLeadCurrentSplit.lean),
the original draft clause was:

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

## 6. Historical proposal for the parent-preserving repair

A historical two-file patch is available at
[N04PulledFields-reference-repair.patch](../../drafts/N04PulledFields-reference-repair.patch).
It changes only `N04RealizationLeadCurrentSplit.lean` and
`N04RealizationLeadCurrentProof.lean`; it leaves
`N04RealizationLeadAssembly.lean`, including the parent statement, unchanged.
At the original audit revision, `git apply --check` accepted the patch
against the audited working tree. That was a patch-context check, not a
Lean compilation result. The implementation has since been applied and
ported to the current lead interface, as recorded in section 9.

The proposal was to thread the parent's
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
the final geometric theorem. The full proof and axiom audit remain required
for the repaired split.

The independent module
[N04PulledFieldsReferenceSplit.lean](../../src/ContinuousFlexibility/Analysis/N04PulledFieldsReferenceSplit.lean)
defines these proposed interfaces in its own namespace and proves their
conditional assembly into the exact unchanged parent. It compiled in
[CI 43419522382](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43419522382)
at `1a8a8648` in 5.0 seconds, without applying the patch to any frozen
definition. This checks the proposed
information flow; it does not prove any of the input obligations. In
particular, it does not resolve separate questions about unrestricted
normalization buffers or the unguarded all-piece tower in a predicate-restricted
`CurrentJetDataOn`.

## 7. Adversarial check: pulled height and the fixed-order test

The extra pulled-height family does not remove the proposed freedom in the
middle. Write `M = (c,d)` for the physical middle of one positive component,
`ψ(r,θ) = (Y(r),θ)`, `χ = ψ⁻¹`, and `h₀(r,θ) = H(r)`. For every admissible
state the matching certificate gives `τ = σ = id` and `Q = 1` on `M × ℝ`.
The exact formulas of `WholePositiveReferenceGauge.lean` therefore give

```math
F_z=\psi\circ\sigma_z,\qquad G_z=\tau_z\circ\chi,\qquad
h_z(G_z(y))=\frac{h_0(\chi(y))}{Q_z(\chi(y))}.
```

Choose an increasing smooth diffeomorphism `Θ` equal to the identity outside
a compact subinterval of `Y(M)`, and replace `Y` by `Θ ∘ Y`. Keep `H`, `τ`, `σ`, `Q`,
the buffer, and all physical data fixed. The new inverse is
`χ̃ = χ ∘ Θ⁻¹`, with the cylindrical lifts understood. The support interval
is invariant under `Θ` and `Θ⁻¹`; off it both maps are the identity.
On it the displayed pulled height is the same for every state as for the
reference, even when `H` has nonconstant or very large derivatives. Thus
its **difference** is zero there, and is unchanged off the support.

Checking the other eight families gives the following preservation argument:

| Families | Effect of this reference change |
| --- | --- |
| Physical height and inverse height | Their actual functions do not use `Y`, so they are unchanged. |
| Forward angle defect | A radial postcomposition does not change the angle. |
| Forward radial coordinate | On the modified physical region current and reference charts coincide; elsewhere both charts are unchanged. |
| Jacobian and inverse Jacobian | The same argument applies to germs of the charts. A bijection fixing the middle pointwise cannot send an exterior point into the middle. |
| Inverse radial coordinate and angle defect | Their old differences vanish on `Y(M)`; postcomposition of those differences by `Θ⁻¹` leaves them unchanged. |
| Pulled height | Its difference is `h₀(χ(y)) * (Q_z(χ(y))⁻¹ - 1)`, which vanishes on `Y(M)`. |

The physical/canonical endpoints, piece labels, samples, and parameter
gradings are unchanged. The endpoint source maps in admissibility use
`W.A` and `X.src`, not the modified `Y`; all endpoint jets of `Y` are
preserved because the modification is supported strictly inside the
middle. Transport Jacobian lower bounds and bounds for `Q` are retained
because those transports and `Q` are not changed. Middle normalization
requires equality with the reference fields, so it is retained as well.
No analyticity assumption rules out this compactly supported modification:
the project's `ContDiff ℝ ∞` is smoothness.

This audit found no additional hypothesis that supplies an absolute bound
for the reference inverse slope in that region. The table is a precise
mathematical preservation argument; a Lean theorem transporting the entire
`GeometryData` certificate has **not** yet been supplied.

For the quantitative obstruction it suffices to fix parameter order
`k = 2`, spatial order `s = 1`, and the base point `z = 0`. On distinct
positive pieces choose interior points `r_n` and compact radial tests `f_n`
with `f_n'(r_n) = 0` and `f_n''(r_n) = 1`. Let `v_n` be their genuine pure
height directions and `v_q` the scalar direction. The local response
lemmas in
[N04PulledFieldsCoefficientMixedVariation.lean](../../src/ContinuousFlexibility/Analysis/N04PulledFieldsCoefficientMixedVariation.lean)
differentiate the total increment `q * (U_ref + t f_n)` and remove the
fixed, generally nonzero `U_ref`. `N03Properties` preserves the literal
radial coefficient at every allowed state, and the middle inverse is
independent of that state. The expected mixed jet of the actual pulled
radial coefficient at a static middle point is therefore

```math
c_n d_n,\qquad c_n=1+3w(r_n)^2>0,\qquad
d_n=\widetilde\chi_n'(\widetilde Y_n(r_n)).
```

There is no omitted canonical interval-length factor here: on positive
pieces, [WholeReferenceGaugeAtlasData.lean](../../src/ContinuousFlexibility/Analysis/WholeReferenceGaugeAtlasData.lean)
sets `left = 0` and `right = 1`, so `canonicalUnitPoint` is the identity.
The displayed derivative is therefore the spatial derivative in the unit
coordinate used by the target current-data estimate.

The pure-direction identities in
[HeightSectorDirections.lean](../../src/ContinuousFlexibility/Analysis/HeightSectorDirections.lean)
give `p_j(v_q) = 1` for every grading order. Consequently, for any proposed
output base `b'` and loss `ℓ`, the exact one-high weight at zero is

```math
\operatorname{oneHigh}(p,b',1+\ell,0;(v_q,v_n))
  =2p_{b'}(v_n)+p_{1+\ell}(v_n).
```

Fix the physical test before choosing its reparametrization. Its grading
values are finite and independent of `Θ_n`. Writing `E_n` and `H_n` for
the unchanged material sample values, choose the inverse slope so that

```math
c_n d_n>
n E_n^n\bigl(1+H_n^{3/4}\bigr)\bigl(1+3p_n(v_n)\bigr)
\qquad(n\ge1).
```

Then `n ≥ b'`, `n ≥ 1+ℓ`, and `n ≥ B` imply, by grading monotonicity and
`E_n ≥ 1`, that this exceeds the required bound
`B E_n^B H_n^(3/4) * (2p_b'(v_n) + p_(1+ℓ)(v_n))`. Every smaller positive
neighborhood contains zero, and directional derivatives do not restrict
the magnitudes of the tangent directions. Thus shrinking the neighborhood
does not avoid this fixed-order test.

**This is still not a formal counterexample to the frozen obligation.**
The remaining construction burdens are explicit:

1. Supply one actual admissible baseline gauge with the full all-piece
   `∀ η, GeometryData η ... b ε` premise, without using an open blueprint
   proof. Existence of a retained start or of good reference jets alone
   does not supply this baseline.
2. Construct the simultaneous smooth diffeomorphisms and prove that they
   preserve the reference-family certificate and all nine complete
   current-data interfaces, including their mixed towers on the same
   parameter neighborhood.
3. Select distinct retained positive components and genuine compact tests,
   then identify the relevant actual `SmoothDirections.D 2` of the spatial
   difference jet with `c_n d_n`. The existing scalar response and sector
   direction lemmas are ingredients, not that final identification.
4. Assemble the diagonal inequality against every possible output base,
   positive radius, loss and material constant. One fixed auxiliary column
   suffices to contradict an all-`η` conclusion, but the premise must still
   hold for every auxiliary column.

## 8. Verified support implementation

At commit `bfea9a79ffb0a3e83598a6c6e39782fe14e09ac5`,
[CI run 43425432541](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43425432541)
compiled or replayed all **16 / 16** `N04PulledFields` support/audit modules.
The complete `quick.log` artifact records:

```text
PulledFields support axiom audit passed: 220 declarations, 197 theorems
```

The owner-based audit checks every declaration in the imported support
modules, including private/generated helpers and transitive dependencies.
It permits only `propext`, `Classical.choice`, and `Quot.sound`; the explicit
axiom prints in that run contain those three axioms. The selector estimate
compiled in 25 seconds, the slot expansion in 3.9 seconds, and the complete
support audit in 120 seconds, all under the unchanged default limits.

This run still failed in the inherited
`WholeReferenceGaugeFixedPotentialReferenceJets` module, so it is not a
complete green CI. At that revision, `N04RealizationPulledFields` remained
open. Neither that support audit nor the verified conditional assembly
was a proof or axiom audit of the node.

## 9. Applied reference-preserving split repair

The updated common task gives each line ownership of its subnode statement
and the required shared definitions and assembly. The implementation now
adds `G.ReferenceData η`, an abbreviation for the same-atlas `ReferenceJets`
already present in the parent current obligation.

The positive geometry conclusion, the geometry and field inputs to the
later subnodes, and the PulledFields conclusion carry this certificate as
an implication. The selection of the neighborhood still precedes the
auxiliary column and its certificate. The source and principal conclusions
retain their existing reference premise. Negative geometry is unchanged
by this repair.

`n04Realization_currentObligation_of_split` carries these implications
through neighborhood restriction and union, and discharges them with the
actual reference certificate supplied by the parent. It still derives
the exact unchanged `N04RealizationCurrentObligation` from the five subnodes.
Neither `N04RealizationLeadAssembly.lean` nor the statement
`N04CoordinatesRealization : N04cStatement` is changed by this repair.

The conditional assembly in section 6 had already verified this information
flow in a separate namespace. Its successful audit is not completion of
the actual subnode. The applied shared definitions and the quantitative
PulledFields proof are subject to the full build and actual node audit
described in section 10.

## 10. Complete pulled-field construction and verification

At `54bf9d13`,
[N04PulledFieldsClosure.lean](../../src/ContinuousFlexibility/Analysis/N04PulledFieldsClosure.lean)
proves `n04PulledFields_obligation`, and the actual
[blueprint theorem](../../src/ContinuousFlexibility/Blueprint/N04Coordinates/Realization/PulledFields.lean)
applies it directly. The proof no longer takes an extra physical coefficient
bound as a premise: the actual corrected coefficient difference certificate
is proved from the retained start and admissibility.

The construction combines the original coefficient increment with the
actual return-correction error, using genuine whole-annulus parameter and
spatial jets. A common low grading base is chosen before every parameter
order; each order's high loss is chosen before the spatial order. The full
physical `H^(3/4)` factor survives strip gluing and transfer to the retained
sample. Actual reference identities restore the parameter-order-zero term.
Moving-point composition then gives the three coefficient current families,
which are combined with the actual left and ν column families on one common
neighborhood.

The final auxiliary-witness reduction first selects one existing same-atlas
reference certificate, then chooses the neighborhood. Only `FieldData` is
transported to other auxiliary columns, since those five physical fields,
their gradings, and their samples are independent of the auxiliary column.
The proof does not transport the full `ReferenceJets` certificate.

The parent declaration and the five-input current assembly retain their
original statements. The updated support audit also explicitly checks the
actual blueprint theorem, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. Completion requires both that target audit and the entire CI
to pass on the branch containing the current lead. Pull request #45 records
the verified commit, run, and audit output; the older CI snapshots in this
note remain historical evidence for their explicitly named revisions.
