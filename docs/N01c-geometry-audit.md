# N01c geometric interfaces and ordinary-flow dependencies

This is a mathematical audit and dependency recommendation, not a counterexample
to the existential `N01Statement`.  The input and output existential witnesses
may differ.  None of the proposed extra geometric facts below has been silently
inserted as an assumption of a completed N01c theorem.

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

## 2. What the present upstream predicates say

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

The second assertion is quantitative simple-root nondegeneracy on the whole
component, not a bound for a perturbed coefficient or flow.  It packages the
root-collar lower bound and the interior lower bound from the manuscript.
The present hypotheses do not give it by a routine compactness argument:
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
- N01c needs the cell specified by `C.cell m\), because this same index
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
`morseTailIndex side k\).  A negative model component inside that block has
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
audit identifies a route for a necessary interface repair; it does not modify
`IsRadialReference`, N01a/b, or claim a counterexample to the full existential
N01 statement.

Finally, the small scales remain distinct:
\(w_0\) has the recorded
\(\exp(-n^{5/2}+C_s n^2)\) upper scale, whereas
\(H_n=\exp(-2n^3/3)\).
No extra factor from \(w_0\) can supply a missing \(H_n^{3/4}\) control weight.
The actual designated-cell localization remains necessary in the coefficient
estimates as well as the flow estimates.
