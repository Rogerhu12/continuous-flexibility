# N01b: retaining the strict support certificates

## The original interface gap

The last conjunct of `N01PartB` requires an actual germ equality:

```lean
∀ z ∈ stateNeighborhood S C base ε, ∀ r ∈ Ioo D.a D.b,
  deriv D.w r = 0 → stateProfile D S C z.1 =ᶠ[𝓝 r] D.w
```

The original support clauses were:

```lean
-- RadialTrueBorder
Function.support D.chi ⊆ {r | r ∈ radialCore D ∧ 0 < deriv D.w r}

-- controlGeometryConditions
∀ m, ContDiff ℝ ∞ (C.control m) ∧ HasCompactSupport (C.control m) ∧
  Function.support (C.control m) ⊆ Ioo (C.left m) (C.right m)
```

Ordinary support containment and `HasCompactSupport` do not imply vanishing
on a neighborhood of a boundary point. A smooth function can be zero for
`t ≤ 0`, equal to `exp (-1 / t²)` for small positive `t`, and cut off before
`t = 1`. It has compact topological support and ordinary support in `(0, 1)`,
but it is not identically zero on any neighborhood of zero. Even the vanishing
of every jet at zero does not supply the required germ.

Thus the old support clauses do not justify the germ argument for a supplied
Part A witness. This observation alone is not a counterexample to the entire
existential `N01bStatement`: the actual upstream constructions choose better
controls. The repair retains the stronger property those constructions already
prove.

The manuscript uses precisely that property. In
[`07-fixed-geometry.tex`](../../paper/flexible-surface-readable/07-fixed-geometry.tex),
the travel-angle controls are constructed from a smooth bump supported away
from the root, and the type argument in Lemma 7.7 says that the controls vanish
near every root. It also uses a positive minimum of `w_*' / w_*` on the compact
border support.

## Exact interface repair

Only the two support sets above change from `Function.support` to `tsupport`.
The local-finiteness clause remains a statement about ordinary supports. All
other fields, including the true border pairing, optical travel derivative,
control jet bounds, state profile, and the full output of `N01PartB`, retain
their definitions.

This is an explicit strengthening of the support certificates in the shared
geometry predicates; it is not a deduction of strict support from the old
weaker predicates. The theorem declaration
`N01b (hN01a : N01aStatement) (hS05 : S05Statement) : N01bStatement`
retains its argument and result names. Their shared geometric definitions now
retain the support information needed for the manuscript's germ conclusion.

The compatibility lemmas `RadialTrueBorder.support_subset` and
`controlGeometryConditions.support_subset` recover the former ordinary-support
inclusions using `subset_tsupport`. In the current main-based proof library,
the direct ordinary-support consumers needing adjustment are
`StateProfileRegularity.stateControlSum_zero_off_core` and the two applications
of the off-component derivative lemma in `StateControlDecay`. No analytic
closure, inverse, or germ conclusion is added to an upstream hypothesis.

## Actual optical-control construction

The inspected `line/N01a` source is fixed at commit
`1e067d5bfc4e9655c33b8af7ba594419658f90cd`.

- [`N01aOpticalControls.lean`](https://github.com/Rogerhu12/continuous-flexibility/blob/1e067d5bfc4e9655c33b8af7ba594419658f90cd/src/ContinuousFlexibility/Analysis/N01aOpticalControls.lean)
  proves `exists_n01a_uniform_opticalControls`. Its output includes
  `tsupport (χ i) ⊆ Ioo (l i) (h i)`, the actual unit optical-travel derivative,
  and uniform bounds for every ordinary derivative. It invokes the proved
  `tsupport_n01aOpticalControl_subset` for the normalized actual control.
- [`N01aControlGeometryAssembly.lean`](https://github.com/Rogerhu12/continuous-flexibility/blob/1e067d5bfc4e9655c33b8af7ba594419658f90cd/src/ContinuousFlexibility/Analysis/N01aControlGeometryAssembly.lean)
  already takes that strict support certificate in
  `n01aGeometryOfControls_controlGeometry`. Its former assembly discards the
  stronger certificate by passing through `subset_tsupport`.

For integration against the repaired predicate, its support-field constructor
changes only from

```lean
exact ⟨(hχ m).1, (hχ m).2.1, hsupp m⟩
```

to

```lean
exact ⟨(hχ m).1, (hχ m).2.1, (hχ m).2.2⟩
```

The local `hsupp` proof is still used for local finiteness. The actual controls,
their normalization, the quantitative estimates, and their enumeration do not
change.

## Actual normalized central border

The inspected `line/R10a` source is fixed at commit
`7e5346dc5e74ced9bbe80f29d3de779f4b1e3ee6`.

[`CentralTrueBorder.lean`](https://github.com/Rogerhu12/continuous-flexibility/blob/7e5346dc5e74ced9bbe80f29d3de779f4b1e3ee6/src/ContinuousFlexibility/Radial/CentralTrueBorder.lean)
proves `exists_central_true_border` by choosing an actual central bump, proving
its pairing is nonzero, and dividing by that pairing. Its output includes

```lean
tsupport χ ⊆ Ioo l h
∀ r ∈ tsupport χ, 0 < deriv w r ∧ φ r * deriv φ r < 0
(∫ r in a..b, radialJacobi 4 (fun t => w t * χ t) φ r * φ r) = 1
```

The bump's closed support lies in a strictly smaller closed interval inside
`Ioo l h`; division by the pairing preserves that containment. These are
properties of the constructed, normalized border, without a root-germ
assumption.

Two constructors expose this same certificate:

1. In [`ReferenceTrueBorder.lean`](https://github.com/Rogerhu12/continuous-flexibility/blob/7e5346dc5e74ced9bbe80f29d3de779f4b1e3ee6/src/ContinuousFlexibility/Radial/ReferenceTrueBorder.lean),
   `exists_reference_true_border_controls` already obtains `hχcap` and
   `hχsign` on `tsupport χ`. The repaired `hborder` branch is simply

   ```lean
   intro r hr
   have hrinterval := hχcap hr
   exact ⟨⟨haright.trans hrinterval.1, hrinterval.2.trans hhb⟩,
     (hχsign r hr).1⟩
   ```

   The former intermediate `hrclosed := subset_tsupport χ hr` is removed.

2. In [`FixedCentralBorder.lean`](https://github.com/Rogerhu12/continuous-flexibility/blob/7e5346dc5e74ced9bbe80f29d3de779f4b1e3ee6/src/ContinuousFlexibility/Radial/FixedCentralBorder.lean),
   the actual `FixedCentralBorder` structure already stores
   `chi_support : tsupport chi ⊆ Ioo fixedCentralCapLeft fixedCentralCapRight`.
   In `FixedCentralBorder.install`, the only corresponding change is

   ```lean
   have hi := B.chi_support hr
   ```

   in place of `B.chi_support (subset_tsupport B.chi hr)`. The existing central
   model derivative identity supplies strict positivity there. The normalized
   annular pairing and the installed physical column remain the same.

These upstream files are evidence and integration instructions at the exact
commits above. This support repair does not import their entire branches or
modify those remote branches.

## Germ proof after retaining the certificates

`Analysis/NeighborhoodRootGerms.lean` proves the local consequence directly.
At a zero of `deriv D.w`, strict support excludes the point from every control's
topological support. Local finiteness reduces the relevant controls near that
point to a finite set, so their individual zero neighborhoods have a common
zero neighborhood. Strict positive support excludes the same point from the
border's topological support. The exponent in the actual `stateProfile` is
therefore zero on that neighborhood, for every state. This proves actual
function equality near the root, rather than only equality of derivatives at
the root.
