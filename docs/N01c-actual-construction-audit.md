# N01a primitive construction audit

The repaired N01a implementation constructs `N01PrimitiveGeometry` on the
actual reference returned by the closed R11a geometry construction. It keeps
that reference's cells, uses the normalized optical controls' actual host
map, proves the required bounded additive index shift, and supplies the
uniform pointwise optical lower bound. A fixed-reference inverse completion
then retains these geometric facts in the resulting `RadialReference`.

The actual construction and repaired N01a node passed the full build at
`1fedc057fbca5bda71bb1006eefd72f67f8aea2b`; section 8 records that evidence.
This document preserves the original construction gap as history and
records how each clause is now discharged.

## 1. Historical finding: the original construction lost the host

This section describes the construction inspected before the repair. Its
claims about missing information are historical; the current construction
is described in sections 3–7. The original finding concerned the supplied
construction and did not assert a counterexample to existential N01a.

The earlier `Blueprint/N01a.lean` eliminated
`hR12 : Nonempty RadialReference`, grouped that witness's cells through
`exists_n01a_grouped_reference`, and applied
`n01aStatement_of_quantitative_reference`.

The earlier `N01aFinalAssembly.lean` obtained controls and a genuine host map
from `exists_n01a_opticalControls_of_radialReference`. It then obtained an
equivalence `e : ℕ ≃ N01aNegativeComponent D` with the estimate

```lean
∀ n, (D.cellIndex (host (e n)) : ℝ) ≤ B * (1 + (n : ℝ))
```

The host map was used for control-jet estimates. The final
`n01aGeometryOfControls` in `N01aControlGeometryAssembly.lean` set

```lean
cell := id
left := fun m => (e m).left
right := fun m => (e m).right
```

The repaired primitive contract requires the exact clause

```lean
∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)
```

For that earlier identity-cell assignment, this would require
`(e m).interval ⊆ D.cells m`. The available `hhost` instead supplied
`(e m).interval ⊆ D.cells (host (e m))`. The grouped-reference index lower
bound and the linear enumeration estimate did not identify those physical
cells.

Changing only `cell := id` to `cell := fun m => host (e m)` would also have
required the original Part A clause

```lean
∃ B : ℝ, 0 < B ∧ ∀ m,
  |(D.cellIndex (host (e m)) : ℝ) - D.cellIndex m| ≤ B
```

The linear upper bound `hostIndex ≤ B * (1 + m)` does not supply this
bounded additive difference. The additive clause is retained in the
current `N01PartA`; the repair proves it using the actual cell geometry.
The earlier identity-cell assignment did satisfy the original additive
clause. The missing argument was to establish it together with actual
designated-cell containment after retaining the genuine host map.

## 2. Historical finding: upper jets and travel did not supply a pointwise lower bound

The additional primitive assertion is exactly

```lean
∃ K : ℝ, 0 < K ∧ ∀ m r,
  r ∈ Ioo (C.left m) (C.right m) →
  K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
    min (r - C.left m) (C.right m - r) ≤
      -deriv D.w r / (r * D.w r)
```

The original `N01aOpticalProfile.lean` supplied upper bounds for optical
radicand jets and a quantitative lower bound for total optical travel.
Neither assertion alone gives the displayed pointwise estimate. The
componentwise simple-zero lower bound in `N01cFiniteHeadOpticalBounds.lean`
also does not, by compactness alone, provide a common rate for an
accumulating sequence of components. These distinctions remain valid;
the repair supplies the missing quantitative tail argument.

The closed-support clause already followed from `RadialTrueBorder`:

```lean
tsupport D.chi ⊆ {r | r ∈ radialCore D ∧ 0 < deriv D.w r}
```

This gives `tsupport D.chi ⊆ radialCore D` on the same reference. The new
proof uses that existing strict support assertion.

Before R11a landed, the identified route was to retain the concrete
`MorseChainRealization`, the two actual dilations, the central component,
and the cell labels from the geometry factory through a companion proof.
The public `R12Statement = Nonempty RadialReference` had already forgotten
that construction data. Adding a desired estimate to an interface would
not have established it. Main
`93f5906c14e93f96e5f731719c65c5330c16e9a5` supplied the closed R11a
construction and its `R11aRetainedCoordinates`, making the same-reference
proof below available without changing a public radial contract.

## 3. The actual reference and its retained cells

[`r11a_exists_quantitative_geometry_family`](../src/ContinuousFlexibility/Radial/R11aRetainedFamily.lean)
returns the actual `SeedRetainedPair P`, `ConnectedReferenceGeometry Γ`,
the identity `Γ.reference.w = P.pair.profile`, construction geometry, and
`R11aRetainedCoordinates P Γ`. These coordinates record the original
two-tail labels, the final index floor, the pullback inclusion into each
final cell, both tail dilation identities, and a uniform bound on the
number of cells having any one label.

Writing `D₀ := S.family S.sigma` and `D := Γ.reference`, the retained index
relations have the following form:

```lean
D₀.cellIndex = morseTwoTailAt S.chain.index (fun _ k => S.chain.index + k)
D.cellIndex = fun m => max (D₀.cellIndex m) N
```

For the retained order isomorphism `e`, the cells satisfy

```lean
∀ m, e ⁻¹' D₀.cells m ⊆ D.cells m
```

The relation is an inclusion because the actual construction saturates
cells. No equality of the two physical cell families is used. On each
retained tail, `e.symm` is exactly multiplication by the corresponding
`P.pair.radiusL` or `P.pair.radiusR`. Those identities send points of an
original tail cell into the corresponding final cell. The profile
identities also transport the negative components under the same
dilations; a whole component's containing cell is supplied separately by
the actual host map.

All subsequent geometric lemmas concern this one `Γ.reference`. The
current N01a entry point uses the closed retained constructor to choose
its witness with these proved properties. The public `R12Statement` and
`IsRadialReference` definitions retain their existing contracts.
This proves an existential N01a statement using that chosen witness. It
does not certify every arbitrary `RadialReference`, enrich an arbitrary
witness extracted from the entry point's `hR12` argument, or assert
equality with the earlier grouped witness.

## 4. Canonical enumeration and the actual control host

[`exists_n01c_canonical_component_enumeration`](../src/ContinuousFlexibility/Analysis/N01cCanonicalComponentEnumeration.lean)
enumerates the central negative component and the two actual Morse tails.
The classification lemma
[`n01c_morse_negative_tail_model_component`](../src/ContinuousFlexibility/Analysis/N01cMorseComponentClassification.lean)
retains the lower bound on the model index from the starting seam. It also
places the whole model component inside that tail. The glued profile's
negative-derivative classification proves that this enumeration is
exhaustive. Model ordering, the separation of the tails from the central
component, and the actual dilation identities prove injectivity.

For a tail slot, the proof chooses an original cell containing the model
component's midpoint and having the model's index. After pullback, the
scaled midpoint lies in a final cell with exactly the slot's floored
model label, and also in the control's supplied host cell. The argument
does not require a unique model cell or place the whole component in
that midpoint cell. The theorem
[`exists_n01c_overlappingCell_indexBound`](../src/ContinuousFlexibility/Analysis/N01cOpticalCellComparison.lean)
proves that two actual cells sharing a point have uniformly bounded
additive index difference. Its proof uses the already constructed material
coordinate: both cell labels differ by at most a fixed constant from the
same endpoint coordinate, so their difference is bounded by twice that
constant. The single central slot is absorbed into a finite enlargement
of the bound.

The retained-construction wrapper
[`SeedRetainedPair.n01c_component_enumeration`](../src/ContinuousFlexibility/Analysis/N01cRetainedComponentEnumeration.lean)
discharges the canonical lemma's geometric inputs from the closed R11a
metadata and coordinates. Its conclusion applies to every supplied host
map satisfying actual containment:

```lean
∀ host : N01aNegativeComponent Γ.reference → ℕ,
  (∀ J, J.interval ⊆ Γ.reference.cells (host J)) →
  ∃ e : ℕ ≃ N01aNegativeComponent Γ.reference, ∃ B : ℝ, 0 < B ∧
    ∀ m,
      |(Γ.reference.cellIndex (host (e m)) : ℝ) - Γ.reference.cellIndex m| ≤ B
```

Consequently, N01a can first construct its normalized optical controls
and genuine containing-cell map, then enumerate those same controls.
The proof supplies the required additive shift for that map, with the
reference and its cells fixed throughout.

## 5. Uniform optical lower bound on the same reference

[`SeedRetainedPair.n01c_radialPrimitiveGeometry`](../src/ContinuousFlexibility/Analysis/N01cActualPrimitiveGeometry.lean)
proves `N01RadialPrimitiveGeometry Γ.reference` from the actual selected
tail, glued profile, construction geometry, and retained coordinates.
Its arguments are outputs of the closed construction.

The proof has three quantitative ingredients.

1. **Each whole Morse component.**
   [`N01cMorseOpticalLowerBound.lean`](../src/ContinuousFlexibility/Analysis/N01cMorseOpticalLowerBound.lean)
   bounds the optical ratio below by the distance to the nearer turning
   point, with its explicit model coefficient. The theorem
   [`MorseChainRealization.exists_opticalRatio_radialE_lower_bound`](../src/ContinuousFlexibility/Analysis/N01cMorseOpticalEnvelope.lean)
   replaces that coefficient by one common negative power of `radialE n`,
   simultaneously on both tails for every model index at least 100.
   The actual selected construction starts at an index at least 4096.
2. **The actual physical dilation.**
   [`N01cScaledMorseOpticalCover.lean`](../src/ContinuousFlexibility/Analysis/N01cScaledMorseOpticalCover.lean)
   uses the exact profile identity under radius scaling. The optical
   ratio scales by `radiusScale⁻²`, while component distance scales by
   `radiusScale`; therefore the lower coefficient scales by
   `radiusScale⁻³`. The height scale cancels. Each of the two fixed radius
   scales is absorbed into the common positive constant.
3. **The central component and arbitrary containing hosts.**
   The unique central negative component uses
   [`negativeRadialComponent_optical_lower_bound`](../src/ContinuousFlexibility/Analysis/N01cFiniteHeadOpticalBounds.lean),
   which proves the simple-zero distance estimate. The glued profile's
   negative-derivative cases cover every negative point. The actual
   pullback cells attach model labels to these points, and
   [`exists_n01c_overlappingCell_negativePower`](../src/ContinuousFlexibility/Analysis/N01cOpticalCellComparison.lean)
   transfers the lower weight to any actual host containing the component.

The point-cover assembly in
[`N01cOpticalPointCover.lean`](../src/ContinuousFlexibility/Analysis/N01cOpticalPointCover.lean)
then gives the exact radial certificate:

```lean
tsupport D.chi ⊆ radialCore D ∧
∃ K : ℝ, 0 < K ∧ ∀ l h m,
  NegativeRadialComponent D l h → Ioo l h ⊆ D.cells m →
  ∀ r ∈ Ioo l h,
    K⁻¹ * radialE (D.cellIndex m) ^ (-K) * min (r - l) (h - r) ≤
      -deriv D.w r / (r * D.w r)
```

The constant precedes the component, host, and evaluation point. This
uniformity supplies the rate that was absent from the original abstract
reference interface.

## 6. Fixed-reference inverse completion

The companion theorem
[`n01c_actual_reference_with`](../src/ContinuousFlexibility/Analysis/N01cActualReferenceWith.lean)
retains an arbitrary property `Q Γ.reference` proved from the actual R11a
construction. It then constructs the inverse on that same reference.
For the N01a application, `Q` is the conjunction of the radial primitive
geometry and the host-enumeration conclusion from sections 4–5.

The implementation reuses the completed matching family. Its inner and
outer regional estimates have constants chosen before the modal index.
[`n01cReferenceInverseAt_of_regional_envelopes`](../src/ContinuousFlexibility/Analysis/N01cRetainedRegionalEnvelope.lean)
assembles those estimates into a modal envelope, uses the actual finite
cell-label fibers, and constructs `N01cReferenceInverseAt D`.

[`n01cReferenceInverseAt_radialReference`](../src/ContinuousFlexibility/Analysis/N01cRetainedReferenceCompletion.lean)
then applies the existing first-normal inverse estimate, natural-kernel
construction, dense smooth-core closure, positive graph closure, and
Green reciprocity proofs, all with `D` as a fixed parameter. The result is

```lean
∃ D : ReferenceData, IsRadialReference D ∧ Q D
```

The conclusion retains the original reference data, profile, cells, and
localizers. Only the inverse estimates and their constants are completed.
This is the required connection between the concrete geometry and a full
`RadialReference`.

## 7. Assembly into the repaired N01a statement

[`exists_n01c_actual_n01a_reference`](../src/ContinuousFlexibility/Analysis/N01cActualN01aReference.lean)
applies the fixed-reference constructor to the two proved geometric
properties. It returns one actual `RadialReference` together with its
radial primitive certificate and the enumeration theorem for any genuine
containing-cell map.

[`n01aStatement_of_quantitative_reference`](../src/ContinuousFlexibility/Analysis/N01aFinalAssembly.lean)
constructs the affine material data and physical spaces on this reference,
obtains the normalized optical controls and their real hosts from
`exists_n01a_opticalControls_of_radialReference`, and applies the canonical
enumeration theorem to those hosts.

The final control assembly
[`exists_n01c_controlGeometry_with_hosts`](../src/ContinuousFlexibility/Analysis/N01cActualControlAssembly.lean)
uses

```lean
{ n01aGeometryOfControls S e χ x with cell := fun m => host (e m) }
```

The component endpoints, normalized controls, and reference state come
from the same construction. Containment follows from `hhost`; the Part A
index condition follows from the canonical enumeration; and control-jet
bounds remain measured at the real host's label. The proved comparison
`radialE_cell_rpow_le_E0` converts the discrete radial envelope into the
sampled material envelope at `T.sample (C.cell m)`.

Finally,
[`n01PrimitiveGeometry_of_radialConstruction`](../src/ContinuousFlexibility/Analysis/N01cPrimitiveGeometry.lean)
converts the radial lower bound to the exact sampled lower bound in
section 2. The affine material data already satisfy `1 ≤ T.E0` on the
reference interval. The negative-power comparison therefore uses the
same material data and the same host samples as the control estimates.

[`Blueprint.N01a`](../src/ContinuousFlexibility/Blueprint/N01a.lean) now
invokes this actual constructor and establishes the repaired conclusion

```lean
∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
  ∃ C : NonlinearGeometryData S,
    IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
      N01PartA A.val T S C ∧ N01PrimitiveGeometry A.val T S C
```

Its public theorem signature remains unchanged. No coefficient, speed,
or flow tame conclusion is assumed to obtain the primitive certificate.
N01b replaces the flow and inverse fields while preserving the reference,
material data, spaces, component endpoints, control functions, and host
map. Its certificate transport uses those preserved fields. The
coefficient, speed, and flow stages then establish the public theorem
`N01c (hN01b : N01bStatement) : N01Statement` with the documented repaired
predecessor and flow contracts. Preserving that outer theorem signature
does not claim a proof with the old contracts unchanged.

## 8. Validation and final integration evidence

The actual construction first passed the complete branch build at
[`1fedc057fbca5bda71bb1006eefd72f67f8aea2b`](https://github.com/Rogerhu12/continuous-flexibility/commit/1fedc057fbca5bda71bb1006eefd72f67f8aea2b),
in [CI run 43183467191](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43183467191).
That run completed 6,437 jobs and reported **2,462 / 2,464 modules
compiled**, with the two existing root exclusions unchanged. Its blueprint
report listed **11 statements open** and moved N01a into the proved set.

The repaired `Blueprint/N01a.lean` keeps its exact public theorem
signature and a `#guard_msgs` check for

```text
'ContinuousFlexibility.Blueprint.N01a' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Successful compilation of that file enforces the displayed transitive
axiom result. The same run passed the strict gate for `N01cCoefficients`,
`N01cSpeeds`, `N01cFlows`, and `N01c`, permitting only `propext`,
`Classical.choice`, and `Quot.sound`.

This is the construction-closure checkpoint. The final latest-main merge,
its exact two-parent ancestry, complete CI run, module count, open
statement list, and ready-for-review transition are recorded in the final
report of [PR #23](https://github.com/Rogerhu12/continuous-flexibility/pull/23).
The acceptance check is the complete build of that actual merged head,
including both N07b restriction consumers, the seven later N08 flow
consumers, and both N07a flow consumers. See
[the flow-quantifier migration notes](N01c-flow-quantifier-migration-notes.md)
for those changes. The lead-owned `docs/STATUS.md` remains the project
ledger.
