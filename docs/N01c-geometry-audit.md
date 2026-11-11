# N01c geometric interfaces and ordinary-flow dependencies

Sections 1–9 audit the original interfaces; section 10 records the construction
evidence and its status at that audit update. Section 11 records the explicit
repair and the later strict-support compatibility changes. This is not a counterexample to the
existential `N01Statement`: the input and output witnesses may differ. The repair
retains primitive reference geometry, never a coefficient, speed or flow tame
conclusion. Completion of N01c still requires its three actual proof stages.

## 1. Exact type calculation

For the actual corrected coefficient fields the already proved theorem
`polar_corrected_determinant` in `Scalar/TypeCorrection.lean` gives

```
a c - b² = (w w′ / r) / D².
```

The `w` here is the actual controlled profile `stateProfile D S C z.1`, not
`D.w`.  Therefore, with the positive profile, radius and height discriminant,
and with `Q ≠ 0`, the square-root argument `b² - a c` is positive if and only if
`deriv (stateProfile D S C z.1) r < 0`.  The already proved
`polar_corrected_determinant_neg_iff` establishes precisely this equivalence.

The new `N01cSpatialCoefficients.lean` applies those identities to the genuine
N01 profile and integral height.  It proves all three actual coefficients are
spatially `ContDiffOn` on the whole open annulus, identifies the exact negative
type domain, and proves the actual minus characteristic speed smooth there.
It does not infer type preservation on a reference component without a premise.

## 2. What the original upstream predicates recorded

`N01PartA` contains reference negativity on `(C.left m,C.right m)`, endpoint
simple zeros, compactly supported smooth controls in those intervals,
local finiteness, unit optical-travel variation, an index comparison for the
chosen `C.cell m`, and absolute all-order control derivative bounds.

`N01PartB` contains the given classical ordinary flows, chart/inverse properties,
the bounds for `w/w*`, `Q/w`, `D`, and equality of profile germs at old roots.
It does **not** contain the manuscript's assertion that the positive and
negative components are unchanged.  Its root-germ assertion permits additional
critical points in an interval's interior.  At `q = 0`, even an interior change
of sign is compatible with the listed ordinary flow conditions: the totalized
real square root gives a continuous radial speed, and its integral is still an
angle translation with derivative one.  This observation explains why the
ordinary ODE clause cannot simply be substituted for type preservation; it is
not a constructed counterexample satisfying all existential N01 data.

`RadialProfileGeometry` requires `w″ ≠ 0` at roots, but gives no quantitative
lower bound for those second derivatives across the accumulating components.
`AccumulatingProfileBounds` bounds the jets of `w` and `1/w` from above.  Neither
condition supplies a lower bound for `|w′/w|` away from a root, or for its
normalized simple-zero factor.

Even a uniform quantitative endpoint Morse bound alone would not replace the
interior estimate.  For `0 < ε ≤ 1`, consider on `0 < s < 1`

```
qε(s) = s(1-s) (ε² + (s-1/2)²).
```

All its fixed-order raw derivatives are uniformly bounded; its endpoint
simple-zero slopes have absolute value `ε² + 1/4 ≥ 1/4`; and it is positive
throughout the interior.  Nevertheless

```
(sqrt qε)″(1/2) = 1/(2ε) - 2ε.
```

At this point the endpoint-distance weight is a fixed nonzero constant.  The
genuine smooth positive radial profile
`wε(r) = exp(-∫₁ʳ t qε(t-1) dt)` on `[1,2]` realizes
`-wε′/(r wε) = qε`, with uniformly bounded fixed-order jets of both `wε` and
`1/wε`.  This is a local demonstration of the missing square-root estimate,
not a profile claimed to satisfy the full global spectral N01 hypotheses.

There is also a localization issue: `RadialReturnMargins` supplies some cell
containing each actual negative component; `N01PartA` does not assert this is
the selected `C.cell m`.  A bound comparing `cellIndex (C.cell m)` with
`cellIndex m` alone does not locate the component in that cell.

## 3. Minimal useful geometric additions

The smallest *qualitative* correction faithful to manuscript Lemma 7.7 is the
following actual geometric conclusion in the upstream neighbourhood:

```
∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
  r ∈ Ioo (C.left m) (C.right m) →
  deriv (stateProfile D S C z.1) r < 0.
```

This is not a speed tame estimate.  It is sufficient for the spatial smoothness
clause by the new `n01_minusCharacteristicSpeed_contDiffOn_component` theorem.
It is not sufficient for all-order endpoint-weighted quantitative bounds.

A compact reference-geometry interface sufficient for the needed quantitative
work is:

1. `Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)` for every `m`, retaining
   the existing bounded index shift.
2. Define the actual reference squared optical speed
   `Q₀ r = -deriv D.w r / (r * D.w r)` and
   `δₘ r = min (r - C.left m) (C.right m - r)`.
   There is one `B > 0` such that on every reference negative component

   ```
   B⁻¹ * (T.E0 (T.sample (C.cell m)))^(-B) * δₘ r ≤ Q₀ r.
   ```

3. The true scalar border has closed support in the open core:
   `tsupport D.chi ⊆ radialCore D`, retaining the existing compactness and
   ordinary-support positivity. This is sufficient for the finite-cell bounds
   and its vanishing on negative components. Section 8 explains why the
   original ordinary-support clause does not imply the closed-support fact.

The second assertion is quantitative simple-root nondegeneracy on the whole
component, not a bound for a perturbed coefficient or flow.  It packages the
root-collar lower bound and the interior lower bound from the manuscript.
The original hypotheses do not give it by a routine compactness argument:
compactness gives a different positive constant in each component, while the
theorem requires a controlled coefficient power uniformly in the component.

Why these additions suffice for the missing local ingredients:

- The reference `w`, `1/w` jet bounds and the localization give all fixed-order
  upper bounds on the actual `Q₀` by coefficient powers.
- Since a control is smooth and supported inside the component, all its jets
  vanish at both endpoints.  In particular
  `|χₘ′(r)| ≤ δₘ(r) sup |χₘ″|`.  Combined with the displayed lower bound, this
  bounds `χₘ′/(r Q₀)` by a coefficient power.  No separate uniform distance of
  the control support from the roots is needed for this zero-order argument.
- For higher derivatives, on each half divide both numerator and denominator
  by the distance to its nearer root using
  `g(x)/x = ∫₀¹ g′(t x) dt`.  The normalized denominator is bounded below by
  a coefficient power and has derivative bounds from the reference jets.
  Smooth reciprocal calculus gives the desired coefficient-power bounds for
  every derivative of `χₘ′/(r Q₀)`; this costs actual finite derivatives of
  `χₘ` and `Q₀`, not an assumed derivative tower.
- On a negative component, the compact positive-side control vanishes, and
  disjointness makes all other component controls vanish there.  Thus the
  actual logarithmic perturbation is `f = κₘ χₘ` locally.  The weighted bound
  for `κₘ`, the index comparison and the `H^β E^A` absorption give, after one
  neighbourhood shrink, `|f′/(r Q₀)| ≤ 1/2`.  Consequently
  `-w′/(r w) = Q₀ - f′/r` lies between `Q₀/2` and `3Q₀/2`.
- The same normalized-root calculation bounds derivatives of `sqrt Q₀`
  with the endpoint powers used by the flow target.  On root collars it also
  supplies the smooth positive factor `cᵢ` in `sqrt Q₀ = sqrt x * cᵢ(x)` and
  bounds its reciprocal, so the manuscript's regularized flow applies.

Merely adding qualitative sign preservation would leave the reciprocal and
normalized-root estimates above unproved.  Conversely, adding a full
`CharacteristicSpeedTameBounds` hypothesis would assume the next target and
is not an acceptable repair.

## 4. Precise manuscript evidence and existing geometric proof inputs

In `paper/flexible-surface-readable/07-fixed-geometry.tex`:

- Lines 526–554 introduce `v₀ = sqrt(x) cᵢ(x)`, give the quantitative root
  factors and their reciprocal derivative bounds, and choose one root collar
  before any differentiation order.
- Lines 607–644 construct normalized controls.  On their support they bound
  both `v₀` and `|w*′/w*|` by explicit powers of the model scale.
- Lines 691–707, Lemma 7.7, explicitly say that the positive/negative components
  stay the same.  Its Step 2 (lines 741–751) proves the relative estimate
  `|κₙ χₙ′| / |w*′/w*| ≤ C |κₙ| Aₙ^(-29)`.
- Lines 1361–1374 prove an interior lower bound on the reference optical speed
  outside root collars.  Along with the collar bounds this yields the proposed
  `Q₀ ≥ coefficient-power * δ` interface.
- Lines 1538–1609 prove the general-state speed estimates using exactly the
  ratio `f′/(r v₀²)` and the smooth root factor.  Positivity is never used as
  an implicit bound for a reciprocal.
- Lines 1019–1040 and 1628–1645 use the fixed-strip regularization
  `Θ_t = 2 x t d(x t²,Θ) + 2 ζ t² c₀(x t²,Θ)`, followed by `ζ = ± x^(3/2)`.

Actual existing Lean inputs, rather than assumed targets:

- `Radial/MorseCellCriticalPoints.lean` proves the exact physical derivative
  and the exact second derivative at a true model root
  (`hasDerivAt_morseCollarExpHeight`,
  `morseCollarExpHeight_second_deriv_at_root`).
- `Radial/MorseRetainedRadiusModelBounds.lean` gives the radius/velocity model
  estimates; `Radial/MorseCellModelJets.lean` and
  `Radial/MorseCellPhysicalJets.lean` give all finite model/physical jet bounds.
- `Analysis/OpticalTravelVariation.lean` proves the true differentiated travel
  integral and normalization from a collar with fixed inverse-flux sign.
- `Analysis/NegativeComponentOpticalControl.lean` proves existence of such
  a collar and a normalized control on every actual negative component, but
  currently only qualitatively.  It does not supply a common coefficient-power
  lower bound on collar width or normalization.

To justify the strengthened geometric interface constructively, use the actual
Morse realization retained by the upstream radial construction and transfer the
explicit `ρ/r_X²` estimates.  The current abstract `IsRadialReference` does not
retain that model realization.  Rechoosing a richer existential witness is a
legitimate route, but reconstructing a new reference with all its spectral and
inverse properties is a substantial additional proof, not a one-line choice.

## 5. The real flow API on Tool-OneHighFactor

Inspected `origin/line/Tool-OneHighFactor` at `b60f900` (read-only).  Four genuine
flow modules are reused unchanged from that branch:

- `OneHighCircleFlowBasic`: `scalar_linearODE_eq_mul_exp`; for a jointly smooth
  flow, derives the angular variational equation, exponential Jacobian formula,
  positivity and bounds from the actual ODE.
- `OneHighCircleFlowIntegral`: continuity and all-order finite-dimensional
  smoothness of parameter-dependent compact interval integrals/primitives.
- `OneHighCircleFlowVariational`: `circleTrajectory_difference_eq_mul_exp`;
  `continuousCircleFlow_hasDerivAt_angle` derives the first angle derivative by
  a genuine finite-difference limit, with no derivative-of-flow hypothesis.
- `OneHighCircleFlowContinuity`: periodic smooth speed plus individual classical
  time trajectories imply joint continuity, the actual angle derivative,
  strict monotonicity and the lift law.  `circleFlow_hasDerivAt_angle` has no
  assumed joint smoothness or angular derivative of the flow.

These APIs require a globally `ContDiff ℝ ∞` speed on the time-angle plane.
The unregularized characteristic speed is generally only square-root regular
at the endpoint.  Applying those theorems directly on the original closed
negative component would therefore be invalid.  Use them on the smooth
fixed-strip root equations and smooth interior pieces, then identify the
assembled trajectory with `C.minusFlow` by actual ODE uniqueness.

The inspected branch does **not** yet provide the full all-order state-parameter
variations and one-high-factor ordinary-flow estimate used in N01c.  In
particular its first-angle derivative theorem is not a substitute for a
`SmoothDirections` tower in the state variable.

The shortest honest dependency route is therefore:

1. retain/prove the quantitative reference nondegeneracy and cell localization;
2. prove relative control and common type preservation;
3. finish actual coefficient and speed one-high-factor bounds, including
   the normalized root equations;
4. reuse the four existing circle-flow modules and extend their finite-
   difference/integrating-factor proof to inhomogeneous parameter variations;
5. induct on genuine parameter jets and spatial jets with the permitted
   parameter-order loss, then identify the flow with the existing N01b witness.

No shortcut from qualitative positivity to uniform reciprocal bounds or from
the totalized `iteratedDeriv` operation to genuine parameter smoothness is valid.


## 6. A direct quantitative theorem from the retained realization

The needed tail estimate can be derived from the existing
`MorseChainRealization` interface.  Recovering the stronger
`MorseChainGeometryWitness` is unnecessary for this step.

The complete proof group in
`Analysis/N01cMorseOpticalLowerBound.lean` has the following concrete
conclusions.  Here \(A=A_n\), \(B=B_n\), \(R=T.radius\;side\;n\),
\(X_L=morseLeftTurn(A,B)\), \(X_R=morseChainRightTurn(T,n)\), and
\(Q_0(r)=-w'(r)/(r w(r))\).

1. `MorseChainRealization.opticalRatio_at_radius` differentiates the
   **actual** identity \(w(R(X))=\mathrm{amplitude}\,R'(X)\) and uses the
   **actual** equation \(R''=-\rho R\).  It gives
   \[
   Q_0(R(X))=\frac{\rho(X)}{R'(X)^2}.
   \]
   Positivity of \(w\) and \(R'\) supplies the nonzero amplitude needed for
   cancellation.  No assumption about the height-choice sequence beyond
   the realization is added.

2. `n01c_morseRho_lower_distance` uses the exact factorization
   \(\rho=A(e^{-X}-t_R)(t_L-e^{-X})\), the existing root bounds, and
   \(e^u(v-u)\le e^v-e^u\).  If \(16B\le3A\), it proves
   \[
   \rho(X)\ge\frac B4\min(X-X_L,X_R-X)
   \quad (X_L<X<X_R).
   \]
   In particular this is a bound on the whole positive lobe, rather than
   only separate information about the two root derivatives.

3. `MorseChainRealization.radius_deriv_le_seven_b_mul_A` normalizes the
   same radius by \(s=R(X_R)>0\), exactly as in
   `MorseRetainedRadiusModelBounds.lean` lines 46–70.  The frozen initial
   slope becomes \( (R/s)'(X_R)=A^5/100\).  The already proved
   `morseLeftCap_radius_bounds` then gives
   \[
   R'(X)\le7sA\le7D.b\,A
   \]
   on the whole retained interval to the left of \(X_R\).  The tail
   condition \(100\le n\), the least-nonsquare choice, and
   `morseChainB_A_bounds` give \(A\le1/1000\),
   \(A^9/9^9\le B\le A^9\), and \(16B\le3A\).

4. The mean value theorem compares physical and model distances.  With
   \(M=7D.b\,A\) and
   \(\delta(r)=\min(r-R(X_L),R(X_R)-r)\),
   \[
   \delta(R(X))\le M\min(X-X_L,X_R-X).
   \]
   Combining this with \(R'(X)^2\le M^2\) proves the explicit result
   \[
   \boxed{\quad
     Q_0(r)\ \ge\
     \frac{B}{1372\,D.b^3 A^3}\,\delta(r)
     \quad\text{for } R(X_L)<r<R(X_R).
   \quad}
   \]
   The final
   `MorseChainRealization.opticalRatio_lower_bound_on_component` is stated
   directly at every such physical \(r\); it obtains the actual coordinate
   by the intermediate value theorem.  It has no assumed optical-speed,
   flow, or tame estimate.

The coefficient is at least
\(A^6/(1372\cdot9^9D.b^3)\).
The proved `morseChainA_exp_bounds` gives
\(A\ge e^{-n^2}/3\).
For comparison with the repository's weights, remember that
\[
E_n=\exp(Q_n),\qquad Q_n=n^{5/2}\log(e+n),
\]
not \(\exp(n^2)\).
The existing `radial_nat_sq_le_Q` permits the weaker but sufficient
\(E_n^{-6}\) lower scale.  Passing to the final material sample weights
still requires the actual cell-index and material-weight comparison.

The proof group also includes `n01c_opticalRatio_dilation`.  From equality
of actual germs \(W(\lambda r)=\mu\lambda w(r)\), with nonzero scales, it
derives
\[
Q_W(\lambda r)=\lambda^{-2}Q_w(r).
\]
Since the corresponding physical distance is multiplied by \(\lambda>0\),
a \(Q/\delta\) lower bound changes by \(\lambda^{-3}\).  The height scale
\(\mu\) cancels.  This is the exact transfer needed for the two tail
dilations in R08.

The finitely many indices below 100 can be handled by continuity of
\(Q_0/\delta\), its positive limits at the two simple roots, and compactness
of each actual model interval.  That finite-head argument and the final
weighted reindexing are separate remaining steps; they are not premises
silently added to the tail theorem.

## 7. Where the same geometric evidence is retained and where it is lost

There are two distinct localization assertions.

- `RadialReturnMargins`
  (`Statements/Radial.lean` lines 546–553) already implies that every
  negative component is contained in **some** actual reference cell.
  Thus existence of a containing cell is available from
  `IsRadialReference`.
- N01c needs the cell specified by `C.cell m`, because this same index
  determines the control and flow weights.  Neither
  `controlGeometryConditions` nor `N01PartA` asserts containment in that
  particular cell.  The bounded shift
  \(|D.cellIndex(C.cell\,m)-D.cellIndex(m)|\le B\) does not attach the
  geometric component to either of those cells.

For the concrete Morse partition the missing association is available by a
specific choice, not an arbitrary relabeling.
`morsePartitionTailCell_covers_block G side k`
(`MorseChainPartitionData.lean` lines 436–457) covers the entire physical
block with the single tail cell.  The exact `morseTwoTailAt_tail` identities
then identify both this cell and its index \(T.index+k\) at
`morseTailIndex side k`.  A negative model component inside that block has
the required same-cell localization.

The interfaces have the following precise scope.

| Interface or construction | Evidence retained |
| --- | --- |
| `MorseChainGeometryWitness` and `morsePartitionReference` | Actual normalized radii, bounded positive radius factors, actual partition, and canonical cell labels. |
| `MorseChainRealization` (`Statements/Radial.lean` lines 656–692) | Actual radius equation, initial slope, profile pullback, positive joins, true core membership, endpoint limits, and localizer regions. These suffice for the quantitative optical theorem in section 6. Whole-block coverage is exported only as pointwise existence of cells with the right index. |
| R05 construction (`MorseChainFullRealization.lean`) | Builds the stronger concrete geometry and partition first, then exports the realization. Its auxiliary \(\phi\) is not by itself the final natural Jacobi kernel. |
| R07 `IsSelectedTail` | Retains the actual family of Morse realizations and the chosen height sequence. |
| R08 (`Statements/RadialTargets.lean` lines 114 onward) | Retains tail dilation equalities for the selected family and preservation of negative components and travel. It does not specify how the new `D.cells` are related to the selected family's cells. |
| R10 and R11 (`Statements/RadialTargets.lean` lines 448–468) | Export the accumulating profile and inverse/border properties without the selected-tail realization or its dilation witness. |
| `IsRadialReference` (`Statements/Radial.lean` lines 566–573) and N01a/b | Do not retain a Morse realization, a quantitative \(Q_0/\delta\) lower bound, or the designated-cell containment needed here. |

Consequently, the short reusable route is to carry the **same** reference's
actual tail realization and dilation evidence through the spectral/border
construction, together with the final cell-index association.  Alternatively,
an upstream geometric interface can export the resulting designated-cell
containment and quantitative \(Q_0/\delta\) estimate directly.  Both are
concrete geometric conclusions; neither is the target speed or flow tame
estimate.

One cannot obtain this by taking the R05 profile and independently attaching
the natural-kernel/common-inverse properties of another existential witness.
Likewise, replacing `C.cell` by an arbitrary containing-cell choice would
require rechecking the index-shift and all control-weight clauses.  This
audit identifies the information needed by the same-witness proof. Section 10
records the necessary construction route; section 11 records the explicit
interface repair. No quantitative optical or nonlinear tame conclusion is
added to `IsRadialReference`. Its border support was subsequently strengthened
by the main-compatible strict-support change described in section 11. No
counterexample to the full existential N01 statement is claimed.

Finally, the small scales remain distinct:
\(w_0\) has the recorded
\(\exp(-n^{5/2}+C_s n^2)\) upper scale, whereas
\(H_n=\exp(-2n^3/3)\).
No extra factor from \(w_0\) can supply a missing \(H_n^{3/4}\) control weight.
The actual designated-cell localization remains necessary in the coefficient
estimates as well as the flow estimates.


## 8. The original missing closed-support certificate

The original `RadialTrueBorder` in `Statements/Radial.lean` asserted
`HasCompactSupport D.chi` and

```lean
Function.support D.chi ⊆ {r | r ∈ radialCore D ∧ 0 < deriv D.w r}.
```

The current contract instead requires this inclusion for `tsupport D.chi`,
as retained from main's strict-support repair. The argument below explains
why the former ordinary-support clause was insufficient; it is no longer
an unresolved closed-support gap in the current `IsRadialReference`.

These assertions do not imply that the closed support is contained in the
open core.  A globally smooth flat function can be nonzero arbitrarily
close to an annular endpoint and vanish at and outside that endpoint.
Its ordinary support lies in the core and its closed support is compact,
but the closed support contains the endpoint.  Thus these assertions alone
do not justify replacing the scalar-control region by a compact subset of
the core, or saying that it meets only finitely many reference cells.

This matters quantitatively.  The `ν` direction carries no material height
weight by itself.  A compact subset of the core meets only finitely many
cells by `AccumulatingProfileBounds`; all positive material weights on
those finitely many samples can then be included in a fixed constant.
There is no such finite reduction for a support that accumulates at an
endpoint.  The recorded upper estimates for `w` cannot replace the missing
`H^(3/4)` factor: their scales are different, as recorded in section 7.

The construction already had the right stronger input before the original
interface discarded it. In
`Radial/BorderNormalization.lean`, `border_pairing_neg` (lines 112–119)
and `border_normalized` (lines 162–181) require

```lean
Function.support χ ⊆ Icc α' β'
```

with `α < α'` and `β' < β`.  Choose that closed interval strictly inside
the positive connector.  Taking closure preserves containment in the
closed interval.  Dividing the actual bump by the nonzero pairing constant
does not enlarge its support.  Hence the actual normalized true border has
closed support compactly contained in the positive region.  This is a
support conclusion about the constructed metric bump, not a coefficient
or flow tame estimate.

The manuscript makes the same choice.
`paper/flexible-surface-rewrite/06-global-reference-inverse.tex`,
lines 862–875, constructs the bump on a positive connector and normalizes
it by the actual border pairing.
`paper/flexible-surface-readable/07-fixed-geometry.tex`,
lines 729–751, applies finite-cell bounds to the compact scalar control and
uses a positive minimum of `w*'/w*` on its support.
The newer shortened rewrite of chapter 7 states the corresponding type
argument in lines 276–313.  The long chapter-7 line references elsewhere
in this audit refer to the readable manuscript.

`Radial/CentralAuxiliaryBorder.lean` does prove compact support statements
for the auxiliary Hilbert column and row.  Those auxiliary objects are
different from the final metric control `D.chi`; their support theorem
cannot be transferred to `D.chi` without the actual final-border
construction.  Likewise, the current `CentralPatch` predicate records
equalities for `D.w` and `D.phi`, and contains no condition on `D.chi`.

## 9. The finite head follows from the original simple-root geometry

`Analysis/N01cFiniteHeadOpticalBounds.lean` gives the following actual
mathematical route, with no additional optical hypothesis:

- `negativeRadialComponent_optical_lower_bound` takes only
  `RadialProfileGeometry D` and
  `NegativeRadialComponent D l h`.  It concludes that there is
  `c > 0` such that, for every `r ∈ Icc l h`,
  \[
    c\min(r-l,h-r)\le
    -\frac{w'(r)}{r\,w(r)}.
  \]
- The proof applies continuous divided differences to `f = -deriv D.w`.
  On the two closed half intervals, respectively,
  `|dslope f l|` and `|dslope f h|` have positive minima.
  At an endpoint their values are the absolute values of the nonzero
  actual second derivatives of `w`; in the interior they are nonzero
  because `w' < 0`.  The denominator `r*w(r)` has a positive finite
  maximum on the closed component.
- `radialProfile_finite_criticalPoints_on_compact` proves that the
  critical points in any compact subset of the core are finite.
  A nonzero continuous divided difference isolates each genuine simple
  critical point, so the closed critical set is compact and discrete.
- `compact_head_negativeRadialComponents_optical_lower_bound` consequently
  gives one positive constant for all actual negative components whose
  two endpoints lie in any specified compact subset of the core.  It
  applies the single-component theorem to the finite set of pairs of
  actual critical points.

This treats the finite head without adding a "finite head" assumption.
It does not make an infinite compactness argument at the accumulating
endpoints.  The quantitative Morse estimate in section 6 is still needed
on the tails, together with actual dilation and cell-index comparison.

## 10. Exact same-reference threading needed upstream

The three primitive facts in section 3 can be named separately and proved
from the actual construction. They cannot be asserted to follow from the
original `N01bStatement` without a proof. That statement is existential:
a defective witness does not disprove its implication to another existential
statement. A proof may choose a new, well-constructed witness, but must
actually establish all properties of that same witness.

The upstream implementation has advanced since the original audit. In
particular, main's R12 and R11b are now proved. The following distinguishes
their retained data from the additional primitive certificate needed here.

1. `R08Statement` chooses the selected tail data and joined reference
   together. Main now retains `RadialConstructionGeometry D`: the
   homogeneous profile equation and `RadialReturnMargins D`. The actual
   construction also proves central and tail dilation identities. These
   identities concern that same reference; independently selected witnesses
   cannot supply them.
2. Main's `R10aStatement`, `R10Statement`, `R11aStatement` and
   `R11Statement` carry this existing `RadialConstructionGeometry D`.
   `R10bStatement` acts on the supplied reference, and `R10_of_nodes`
   retains the same reference and certificate.
3. Main's proved R11b keeps its input reference and inverse while enlarging
   the output weight needed for the first-normal estimate. Its angular
   derivative premise is `SourceDerivativeMember`, without an even-source
   condition on the angular derivative. The local L² premise is `MemLp`,
   so it includes the necessary measurability.
4. Main's proved R12 supplies the natural kernels, travel margins, maximal
   graph, closure and reciprocity on its actual reference and inverse.
   This branch preserves that proof and its public conclusion. No part of
   that already completed inverse or final-border calculation is replaced
   by an admission.
5. The existing public `RadialConstructionGeometry` is not the additional
   closed-support and quantitative optical certificate below. The actual
   sources `Radial/SeedReturnMargins.lean` and
   `Radial/BorderNormalization.lean` identify the relevant construction
   evidence: negative components arise from the actual Morse tails or the
   central patch, and the chosen final bump has a closed supporting interval
   inside the core. The finite-head and Morse estimates in this audit can
   be used with those identities. An enriched construction must still
   produce these additional assertions on the reference that satisfies all
   its original properties; merely choosing another geometric witness does
   not establish that requirement.
6. N01a must construct its controls and their designated cells together
   with the additional primitive certificate on the same data. N01b then
   retains it. Neither step is proved by the transport theorem below or by
   closing the N01c implication.

R08, R12 and R11b are proved on main. R10a and R11a remain open at this
audit update. The stronger common-reference construction required by the
repaired N01a output is still an explicit upstream obligation. An isolated
conditional speed or flow estimate does not complete N01c.

## 11. Explicit repair of the construction contract

The task permits repairing an unusable frozen interface together with the
assembly. The public radial endpoint remains exactly

```lean
def R12Statement : Prop := RadialReferenceStatement
```

where `RadialReferenceStatement = Nonempty RadialReference`. Main's proved
R12 and its existing `RadialConstructionGeometry` are retained. The
original nonlinear predecessor output was exactly

```lean
def N01bStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ base : ℕ, ∃ ε : ℝ,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧ N01PartA A.val T S C ∧
        0 < ε ∧ N01PartB A.val S C base ε
```

That output does not retain the three primitive facts identified above.
The repair explicitly strengthens the N01a and N01b outputs. It does not
claim that the original existential implication has been refuted, or that
the original hypotheses have already been proved to imply the enriched
output.

The separately named `N01RadialPrimitiveGeometry D` records closed
border support in the core and the uniform reference optical lower bound

```lean
∃ K : ℝ, 0 < K ∧ ∀ l h m,
  NegativeRadialComponent D l h → Ioo l h ⊆ D.cells m →
  ∀ r ∈ Ioo l h,
    K⁻¹ * radialE (D.cellIndex m) ^ (-K) * min (r - l) (h - r) ≤
      -deriv D.w r / (r * D.w r)
```

This is an additional certificate for the N01a construction, not the
public conclusion of R12. It must be proved on the very reference whose
natural graph, border and inverse satisfy `IsRadialReference`. Its
construction must retain or recover the actual Morse tail, dilation,
central patch and final-border evidence on that same reference. This is a
real additional upstream obligation; an independent reference cannot
supply it.

`N01PrimitiveGeometry D T S C` records designated-cell containment,
the same closed border support, and the corresponding lower bound with
`T.E0 (T.sample (C.cell m))`. N01a constructs it together with its controls;
N01b preserves it. The coefficient and speed stages retain it on the same
existential data, with proved transport when the material envelope is
normalized. No coefficient, speed or flow tame estimate is added to the
predecessor hypotheses. The separate parameter-order flow-loss correction
is recorded in `docs/N01c-loss-audit.md`.

The later main-compatible support update also changes two underlying
primitive clauses: `controlGeometryConditions` requires
`tsupport (C.control m) ⊆ Ioo (C.left m) (C.right m)`, and
`RadialTrueBorder` requires
`tsupport D.chi ⊆ {r | r ∈ radialCore D ∧ 0 < deriv D.w r}`.
These are genuine strengthenings of `N01PartA` and `IsRadialReference`
through their constituent predicates; `N01PartB` itself is unchanged.
The public R12 conclusion retains its existing type constructor and its
proof uses the strengthened border certificate, with no new admission.
In particular, the closed-core support conjunct of `N01PrimitiveGeometry`
now follows from `IsRadialReference`; it remains in the bundle for its
transport interfaces. Designated-cell containment and the quantitative
optical lower bound remain the additional same-reference construction
obligations. Closing the N01c implication does not construct them.

The ordinary theorem `n01PrimitiveGeometry_of_radialConstruction`
converts a supplied `N01RadialPrimitiveGeometry` certificate to the sampled
material envelope using the proved comparison. It does not construct that
certificate. `n01PrimitiveGeometry_normalizeMaterialE0` preserves it under
the explicit envelope normalization: raising `E0` lowers its negative
powers. Neither theorem assumes a nonlinear tame estimate.

`Blueprint/Assembly.lean` uses the original proved R12 and then the
enriched N01a/N01b outputs along the same dependency chain. The N01a and
N01b task files state the retained construction obligations. Closing the
N01c axiom gate proves its implication under this repaired predecessor
contract; it does not close N01a or N01b. The coefficient, speed and flow
estimates still have to be derived from their actual definitions on one
common neighborhood.
