# N01a primitive construction audit

Inspected `origin/main` (N01a proved there) and the existing `line/N01c` contracts.
This document records an actual unclosed construction obligation; it does not
claim a counterexample to the existential N01a theorem.

## Exact current construction

`Blueprint/N01a.lean` eliminates `hR12 : Nonempty RadialReference`, groups
that witness's cells through `exists_n01a_grouped_reference`, and applies
`n01aStatement_of_quantitative_reference`.

`N01aFinalAssembly.lean` obtains controls and a genuine host map from
`exists_n01a_opticalControls_of_radialReference`. It then obtains an
equivalence `e : ℕ ≃ N01aNegativeComponent D` with

```lean
∀ n, (D.cellIndex (host (e n)) : ℝ) ≤ B * (1 + (n : ℝ))
```

The host map is used only for control-jet estimates. The final
`n01aGeometryOfControls` in `N01aControlGeometryAssembly.lean` sets

```lean
cell := id
left := fun m => (e m).left
right := fun m => (e m).right
```

Thus the proved construction does not retain the genuine containing cell.
The new required clause is

```lean
∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)
```

and would require `(e m).interval ⊆ D.cells m` for this exact data.
Existing `hhost` gives `(e m).interval ⊆ D.cells (host (e m))` instead.
Neither the grouped-reference index lower bound nor the enumeration's
linear host-index bound identifies those two physical cells.

Replacing `cell := id` with `cell := fun m => host (e m)` alone is not a
complete repair. It additionally requires the existing Part A clause

```lean
∃ B : ℝ, 0 < B ∧ ∀ m,
  |(D.cellIndex (host (e m)) : ℝ) - D.cellIndex m| ≤ B
```

The proved upper bound `hostIndex ≤ B * (1 + m)` is weaker than this
bounded additive difference. That bounded shift feeds the nonlinear
sample/weight comparison and endpoint-flat closure; it cannot be dropped.

## Optical lower bound

The required uniform assertion is

```lean
∃ K : ℝ, 0 < K ∧ ∀ m r,
  r ∈ Ioo (C.left m) (C.right m) →
  K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
    min (r - C.left m) (C.right m - r) ≤
      -deriv D.w r / (r * D.w r)
```

`N01aOpticalProfile.lean` proves upper bounds for optical radicand jets
and a quantitative lower bound for the total optical travel. It does
not prove this pointwise lower bound. `N01cFiniteHeadOpticalBounds.lean`
already proves a componentwise lower constant and its uniform finite-head
version; compactness alone supplies no rate for an accumulating sequence.

The branch's own `docs/N01c-geometry-audit.md`, especially sections 6–7,
explicitly records this lost information. The new draft
`N01cMorseOpticalEnvelope.lean` converts the already established actual
Morse lower coefficient to one common negative power of `radialE n`.
It does not identify an arbitrary `IsRadialReference` with that model.

## What is already sufficient

The closed-support conjunct is available directly. The strict
`RadialTrueBorder` condition gives

```lean
tsupport D.chi ⊆ {r | r ∈ radialCore D ∧ 0 < deriv D.w r}
```

and hence `tsupport D.chi ⊆ radialCore D`. No extra construction is
needed for that conjunct.

## Same-witness route if a larger construction repair is undertaken

1. Prove a purely geometric scaffold at
   `SeedGluedPair.exists_accumulating_reference_with_construction_geometry`
   in `Radial/SeedReturnMargins.lean`. That proof still possesses the actual
   `MorseChainRealization`, both actual tail dilations, the positive-head
   exclusion of additional negative components, the central component,
   and the cell-index identities. The optical estimates can use
   `N01cMorseOpticalLowerBound`, `N01cMorseOpticalEnvelope`, and
   `N01cFiniteHeadOpticalBounds`; the physical dilation factor is exactly
   radiusScale⁻³ after normalizing by distance.
2. For containment and bounded shift, retain/prove a component enumeration
   paired with the actual cell labels, using the concrete two-tail
   partition and the finite central head. The currently arbitrary
   weight-ordered enumeration is insufficient by itself.
3. `exists_seedControlledReference_with_property` already transports an
   arbitrary property `Q D` of the same reference. Its use in
   `SeedControlledReference.lean` and `SeedRetainedReference.lean` is the
   common entry point for the proved R10a construction as well as R08.
4. A proved geometric certificate can then be retained along the same
   reference in R10a → R10 → R11a/R11b → R12. The inverse, natural-kernel,
   closure and reciprocity proofs need not be replaced. Adding an
   unproved certificate to these interfaces is not a proof.
5. The present `R12Statement = Nonempty RadialReference` drops this
   certificate. Therefore retaining it through R12 would require an
   explicitly audited contract refinement and corresponding genuine
   construction proof. It cannot be recovered merely from the existing
   existential witness by proof syntax or by choosing an unrelated
   reference.
6. With a genuinely constructed scaffold retained on that same D,
   N01a can keep the supplied containing-cell map, construct controls
   against its samples, and use
   `n01PrimitiveGeometry_of_radialConstruction` for the material-envelope
   comparison. The existing N01b transport and N01c proof can then apply.

No frozen contract, shared source file, or blueprint proof has been
changed by this audit. No desired estimate has been introduced as a new
hypothesis of N01a, and no completed proof has been replaced by an admission.
