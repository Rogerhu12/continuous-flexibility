# N04b: audit of the fixed physical cut

## Scope and status

This audit concerns the exact frozen endpoint

```lean
theorem N04b (hN04a : N04aStatement) : N04bStatement
```

in [the task](tasks/N04b.md). It identifies a geometric compatibility problem
between the fixed physical domains in `N04PartA` and the fixed Tricomi cylinders
in `N04PartB`. It gives the mathematical obstruction argument, states the
analytic bridges that still require Lean proofs, and describes a repair that
preserves the actual operator and the source pairing.

**This document is not a proof of `N04b`, a Lean proof of its negation, or a claim
that the task's completion standard has been met.** In particular, a local
calculation showing that the manuscript's preferred cut moves would not by
itself refute the existential statement: `N04bStatement` can rechoose every
piece of cumulative data. The argument below is designed to apply to an
arbitrary putative witness. Its outstanding formal obligations are listed
explicitly in the last section.

This version reconciles the audit already published at `204e9a6` with the
subsequent coefficient and bounded-corrector work. The four statement files
below are unchanged between the earlier audit's pin `7393d67` and main
`875357e209ac27cdb94c9db0429946daf553d3f3`.

The audited definitions are in
[Blueprint/Statements.lean](../src/ContinuousFlexibility/Blueprint/Statements.lean),
[Statements/Nonlinear.lean](../src/ContinuousFlexibility/Statements/Nonlinear.lean),
[Statements/Analysis.lean](../src/ContinuousFlexibility/Statements/Analysis.lean),
and [Statements/Radial.lean](../src/ContinuousFlexibility/Statements/Radial.lean).
The mathematical construction is in the paragraphs “Travel coordinates,”
“The root coordinate,” “The canonical form,” and “Transmission in the middle”
of [the readable manuscript](../paper/flexible-surface-readable/07-fixed-geometry.tex).

## 1. The clauses imposing the extra invariant

The physical endpoints in `CanonicalData` have no state argument:

```lean
physicalLeft : ℕ → ℝ
physicalRight : ℕ → ℝ
cutRadius : ℕ → ℝ
```

The actual physical domain is defined by

```lean
def physicalPieceOpen (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : Set PolarPoint :=
  Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ univ
```

`N04PartA` requires, for every state in the common neighborhood and sector,
that the actual forward chart and inverse chart be mutually inverse smooth
maps between this fixed strip and `canonicalOpen S K m`. It also requires

```lean
∀ z ∈ U, stateSector S z.1 → ∀ m p,
  p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
  ContDiffAt ℝ ∞ (K.chart z m) p ∧
  ContDiffAt ℝ ∞ (K.height z m) p ∧
  planeJacobian (K.chart z m) p ≠ 0 ∧
  0 < K.height z m p
```

The forward chart is therefore smooth and nondegenerate at both physical
boundary circles. Its angular component is a degree-one lift: in the open
strip the chart sends `p + (0, π)` to `chart p + (0, π)`, and this identity
extends to the boundary by continuity.

For each negative component, the first conjunct of `N04PartB` fixes

```lean
K.physicalLeft (K.cutPair m).1 = C.left m
K.physicalRight (K.cutPair m).2 = C.right m
K.physicalRight (K.cutPair m).1 = K.physicalLeft (K.cutPair m).2
0 < K.cutRadius m
K.left (K.cutPair m).1 = 0
K.left (K.cutPair m).2 = 0
K.right (K.cutPair m).1 = K.cutRadius m
K.right (K.cutPair m).2 = K.cutRadius m
```

Thus a single state-independent physical circle `r = c` divides the component
`(a,b) = (C.left m,C.right m)` into `(a,c)` and `(c,b)`, and both canonical
pieces have the same state-independent interval `(0,R)`.

This is a condition on the actual operator. `canonicalOperator` is defined
using `divergenceOperator (L.coefficients z)`, the actual chart, the positive
height factor, and its Jacobian. `N04PartB` requires its equality on every
smooth canonical test function with the displayed canonical divergence
operator plus a potential. On each negative piece it additionally requires

```lean
(K.coefficients z m).a p = 1
(K.coefficients z m).b p = 0
(K.coefficients z m).c p = -p.1
```

Consequently each half must have the characteristic geometry of
`∂ξ² − ξ ∂θ²` on the same fixed cylinder. The potential and the scalar height
conjugation do not change characteristic curves. The cut-transmission
conjunct is not needed for this obstruction argument.

The manuscript instead divides a component at the level `σ = T/2` of its
state-dependent travel coordinate. If `X_z` is the inverse travel chart, its
physical cut is

\[
  \theta\longmapsto X_z(T/2,\theta).
\]

That is an actual moving curve. Replacing it by a fixed radial circle requires
an additional invariant; it is not a consequence of a diffeomorphism of the
whole component onto `(0,T) × 𝕋`.

## 2. The witness-independent perturbation

Assume for the argument that all data in `N04bStatement` have been chosen.
Choose any of its negative components `(a,b)` and let `c` be its claimed
fixed cut. The strict endpoint inequalities in Part A and the displayed
pairing identities give `a < c < b`.

Write `w = D.w` and

\[
 v_0(r)=\sqrt{\frac{-w'(r)}{r w(r)}},\qquad
 E(r)=1+w(r)^2,\qquad
 \omega(r)=v_0(r)\frac{E(r)}{w(r)}.
\]

The radial hypotheses give `w > 0`, `w' < 0` on the open component, and
simple zeros of `w'` at its two endpoints. Therefore `ω` is continuous on
`[a,b]`, smooth and positive in `(a,b)`, and zero at `a` and `b`.

There is a smooth radial function `f`, supported in a compact subset of
`(a,c) ∪ (c,b)`, such that

\[
 \int_a^b\omega f'=0,\qquad \int_a^c\omega f'=1. \tag{1}
\]

One construction is as follows. Since `ω(a)=0`, `ω(c)>0`, and `ω(b)=0`,
the weight is nonconstant on each half. Smooth compact tests `f_L,f_R`
supported in the respective halves can therefore be chosen with nonzero
pairings `I_L = ∫ω f_L'` and `I_R = ∫ω f_R'`. Integration by parts on their
compact supports proves this assertion from the nonvanishing of `ω'`
somewhere in each half. Then `f=f_L/I_L−f_R/I_R` has (1).

The physical-space realization in `IsSobolevModel` represents this compact
radial function by an actual height-space element. Choose a nonzero real
`δ` sufficiently small and replace the height entry of the reference state by

\[
 u_\delta(r,\theta)=u_{\rm ref}(r,\theta)+\delta f(r).
\]

Keep the profile controls `μ,κ` and the left-chart control `η` equal to zero.
This state, denoted `x_δ`, lies in the common state neighborhood and sector.
There is no restriction in the sector condition excluding a radial height
perturbation. The required smallness follows by scaling one fixed finite
seminorm, not by changing the neighborhood or its witnesses.

At `q=0`, the actual physical height and coefficients do not depend on the
height entry of the state. They are the original radial height `H`, with
`H'=w`, and the matrix

\[
 A_0=\begin{pmatrix}w&0\\0&w'/r\end{pmatrix}.
\]

For the original type-corrected coefficients, let

\[
 d=b/a,\qquad v=\sqrt{b^2-ac}/a.
\]

For the genuine height family `H(r)+q u(r,θ)`, direct differentiation of the
definitions at `q=0` gives

\[
 \dot d=-\frac{1+w^2}{rw}
       \left(u_{r\theta}-\frac{u_\theta}{r}\right),\qquad
 \dot v=-v_0\frac{1+w^2}{w}
       \left(u_r+\frac{u_{\theta\theta}}r\right). \tag{2}
\]

For example, the defining discriminant and denominator have

\[
 D_0=1,\quad Q_0=w,\quad
 \dot D=-2w u_r,\quad
 \dot Q=u_r+(1+w^2)u_{\theta\theta}/r,
\]

and the determinant identity gives
`v=√(-w w'/r) √D/Q`. These yield (2) with the displayed signs. The radial
part contributes `dot d=0` and `dot v=−δ ω f'`. The reference height is
exactly `D.phi(r) cos(2θ)` by `referenceStateConditions`, so its contribution
to both first variations consists only of angular frequency two.

The new modules `N04bOpticalHeightVariation`,
`N04bOpticalCoefficientVariation`, `N04bOpticalBalancedTests`, and
`N04bOpticalBalancedHeight` isolate these algebraic and test-function steps.
Their source content must be distinguished from a green CI result and from
the additional differentiation-under-the-integral and flow-variation steps
below; the latter are not supplied merely by pointwise derivative formulas.

## 3. Cancel the return error to first order

Let

\[
 T=\int_a^b v_0(r)\,dr.
\]

At `(x_δ,0)` the original minus return is `θ ↦ θ−T`, both boundary charts
are the identity, and the actual N02 residual is zero. The same statement
holds on every other negative component.

Let `ρ` be the derivative with respect to `q` of the actual N02 residual at
`(x_δ,0)`. N02's smoothness puts it in the actual circle space. Its decoded
components are even and have zero mean. Indeed, differentiating the genuine
return ODE at the radial state integrates (2) along angular translations.
The reference term remains frequency two. The only radial constant term
is the integral of `−δ ω f'`, which vanishes over the full selected
component by (1); the perturbation is zero in every other component.
Composition with the right inverse chart contributes no extra term at this
base point because the uncomposed even residual is identically zero there.

Set

\[
 v_\eta=-R.\mathrm{inverse}(\rho).
\]

N02 gives that `v_η` is odd and `R.linearPart v_η=−ρ`. At `q=0` the actual
`chartIncrement` is the identity because the left chart is the identity.
Thus N02's derivative formula shows that the affine sector path

\[
 z(q)=\bigl(x_\delta+q(0,(0,(0,v_\eta))),q\bigr)
\]

satisfies

\[
 R.\mathrm{residual}(z(q))=o(q)
 \quad\text{in every graded circle seminorm}. \tag{3}
\]

The path remains in the same open neighborhood for sufficiently small `q`.
The chart control `η` enters neither the physical height nor the profile, so
it does not alter (2). No exact nonlinear solution of the return equation
is being assumed here.

The Fourier multiplier in `circleRotationDifference` on an odd mode
`sin(2jθ)` is `sin(2jT)`, producing the corresponding even cosine mode.
It is not a cosine multiplier. The cancellation above uses N02's actual
inverse theorem and therefore does not need a separate multiplier estimate.

## 4. Extract a smooth effective operator without assuming smooth raw L

This step is necessary. The frozen N03 clauses do not directly state that
the raw fields `L.b` and `L.c` are jointly smooth, and Lean's total `fderiv`
must not be treated as an ordinary derivative at an arbitrary nonsmooth
field.

On one negative open piece, write `F=K.chart z m`, `G=K.inverseChart z m`,
`h=K.height z m`, and `J=det DF`. Part A makes these genuine smooth inverse
charts in the interior, with `h>0` and `J≠0`. Given a smooth local physical
test `u`, choose a globally smooth canonical test agreeing locally with
`(u/h) ∘ G`; a cutoff supported inside the canonical open strip makes this
possible. Locality of `fderiv` then transfers Part B to the local physical
test.

The transferred expression is a genuine local second-order differential
operator whose smooth principal matrix is

\[
 A_{\rm eff}=
 \frac{|J|}{h^2}(DF)^{-1}
       \begin{pmatrix}1&0\\0&-F_1\end{pmatrix}(DF)^{-t}. \tag{4}
\]

The raw divergence operator annihilates locally constant functions exactly.
Consequently the transferred zeroth-order coefficient vanishes. This also
determines its apparently arbitrary potential by smooth chart expressions.
For the characteristic argument it is enough that the transferred operator
has matrix (4); no unproved identification of the raw coefficients with
that matrix is needed. In fact, the reverse coordinate-divergence and gauge
identity identifies its action with `div(A_eff ∇u)`: the smooth transformed
principal density divided by `h²` is (4), and the locally constant test
cancels exactly the remaining zeroth-order term. This uses the genuine
coordinate calculus, not a product rule for unsupported raw fields.

For any fixed physical height test `u`, N03 gives

\[
 B_q u=B_{{\rm orig},q}u-e_q(u),\qquad
 e_q(u)=\operatorname{decode}
   \bigl(L.\mathrm{error}(z(q),R.\mathrm{residual}(z(q)),u)\bigr).
\]

Joint continuity of the N03 smooth family, its linearity in its circle
argument, and (3) imply `e_q(u)=o(q)` in every source seminorm. In fact,
for `q≠0` one can put `R.residual(z(q))/q` into that linear argument and
use continuity at zero; no parameter differentiability of `L.b,c` is
being added.

To use this on characteristics one needs a local Sobolev estimate: for a
compact radial subinterval of the annulus and every finite `j`, a sufficiently
high physical source seminorm bounds the decoded `C^j` norm on that interval
times the angular circle. The concrete norm contains all the required
material-coordinate derivatives. On such a compact interval the material
coordinate change and the positive weights have bounded derivatives and
bounded inverses, so the usual compact Sobolev estimate supplies the bound.
This is a proof obligation, not a consequence of pointwise decode continuity
alone. With it,

\[
 e_q(u)=o(q)\quad\text{uniformly in every compact spatial }C^j\text{ norm}.
 \tag{5}
\]

### Even probes also control the symmetry axes

Only even, π-periodic physical height tests are available. Arbitrary mixed
quadratic jets cannot be prescribed at an angular reflection axis. That
restriction does not prevent coefficient extraction, but it must be handled.

Choose a compact radial cutoff equal to one on a neighborhood of the closed
half-component. On that neighborhood let `P=r` and `Q=cos(2θ)`, extending
them with the cutoff so that they and their products are admissible physical
height tests. For the difference `D_q=B_q−B_orig,q`, define

\[
 \Gamma_{D_q}(P,Q)=D_q(PQ)-P D_qQ-Q D_qP.
\]

Both local operators have zero zeroth-order coefficient. If
`ΔA=A_eff−A_orig`, ordinary product differentiation gives

\[
 \Gamma_{D_q}(P,P)=2\Delta a,\qquad
 \Gamma_{D_q}(P,Q)=-4\sin(2\theta)\Delta b,\qquad
 \Gamma_{D_q}(Q,Q)=8\sin^2(2\theta)\Delta c. \tag{6}
\]

Every left side is `o(q)` in all compact `C^j` norms by (5). Division by
the fixed function `sin(2θ)` is bounded from `C^{j+1}` to `C^j` on smooth
functions divisible by that factor; division by its square loses two
derivatives. Near a zero this is the elementary integral Taylor formula
for division by `θ−θ₀`, and away from the finitely many zeros it is ordinary
smooth division. The matrices in (4) are smooth for each state, so the
divisibility is exact. Applying these fixed division estimates to (6)
establishes

\[
 A_{{\rm eff},q}=A_{{\rm orig},q}+o(q)
 \quad\text{in every compact spatial }C^j\text{ norm}. \tag{7}
\]

This includes the reflection axes; dense-set equality followed by continuity
would not, on its own, justify the needed uniform estimates there.

Part A extends (4) smoothly to each closed physical half. The probe estimates
extend to its endpoints by continuity, with their derivative versions using
the smooth extensions. The same fixed probes also give matching effective
coefficient jets at the fixed cut: their N03 source outputs are smooth on the
whole annulus, and fixed sine division reconstructs one smooth field across
it. No additional interface regularity or smooth dependence of the charts
on `q` is being assumed.

## 5. What the closed chart forces at the roots and the cut

The boundary values of the *forward* chart suffice. The frozen specification
does not explicitly control the inverse chart at canonical boundary points,
so this argument does not use those values.

A physical boundary point cannot be sent to canonical interior. Otherwise
an interior sequence approaching it, followed by continuity of the interior
inverse, would put that boundary point in the physical open strip, contrary
to `MapsTo`. Hence the first component of the forward chart takes a value
in `{0,R}` at each physical boundary. It is constant on each boundary circle
by connectedness. The two boundaries cannot have the same value: on the
compact closed cylinder modulo π the extrema of the first component, and
surjectivity onto every `ξ∈(0,R)`, require the values zero and `R`.

Part of this topology already has a reusable proof on `line/N04Coordinates`:
`canonicalChart_endpoint_radial_eq_boundary` in
`Analysis/CanonicalBoundaryImage.lean` establishes the endpoint image fact,
and `canonicalChart_exists_smooth_endpointInverse` in
`Analysis/CanonicalEndpointInverse.lean` obtains the genuine smooth local
inverse by the inverse function theorem. Those source proofs were checked
at that branch's `7a710c39ca424751134f091be4a2c6f43a379b69`; this audit does
not claim their complete use in a compiled N04b obstruction theorem.

N03 identifies the raw coefficient germs with the original coefficient
germs at every root of `w'`. There they are genuinely smooth. The true
type-correction determinant identity is

\[
 a_{\rm orig}c_{\rm orig}-b_{\rm orig}^2
    =\frac{w w'/r}{D^2}.
\]

For the chosen path the profile is exactly `w`. Thus (4), as the effective
operator of the same local tests, agrees with the original principal matrix
near the physical root and has zero determinant at the root. Taking the
determinant in (4) simplifies to

\[
 \det A_{\rm eff}=-F_1/h^4. \tag{8}
\]

Consequently each true physical root is mapped to `ξ=0`; its paired
artificial cut is mapped to `ξ=R`.

On a physical boundary `F_{1,θ}=0`, and nonzero Jacobian gives
`F_{1,r} F_{2,θ}≠0`. The angular derivative has constant sign, and
π-equivariance forces that sign to be positive. Thus the boundary angular
map is an orientation-preserving degree-one circle diffeomorphism lift.

The estimates (7) also give `a_eff>0` on both closed halves for small `q`,
because the reference value is the positive function `w`. Characteristics
are then graphs over the physical radius. Their images under `F` are the
canonical characteristics `dθ/dξ=±√ξ`. The sign and the nonvanishing of the
radial component follow either from (4), or from the positivity of
`F_{2,θ}²−F_1 F_{1,θ}²` and the fixed sign of `J`. Therefore they reach
the specified boundary components rather than turning inside the strip.

Define the positive root loop on a half by following the inward positive
canonical family from the root to the cut, then the other family back to
the root. Its holonomy lift is conjugate, by the boundary angular chart, to
translation by

\[
 2\tau(R),\qquad
 \tau(R)=\int_0^R\sqrt\xi\,d\xi=\frac23 R^{3/2}. \tag{9}
\]

At `q=0` the physical left and right loop shifts are respectively
`2T_L` and `2T_R`, where

\[
 T_L=\int_a^c v_0,\qquad T_R=\int_c^b v_0.
\]

A degree-one lift conjugacy preserves the average displacement of iterates:
the conjugating map differs from the identity by a bounded periodic
function. Equations (9) for both halves force

\[
 T_L=T_R=\tau(R),\qquad T=T_L+T_R=2\tau(R). \tag{10}
\]

In particular, an arbitrary possible witness is forced to choose the
reference optical midpoint, and each of its two loop holonomies must have
the fixed average displacement `T` at every nearby state. This conclusion
does not assume that its charts were constructed by the manuscript's method.

## 6. Justify variation through the degenerate roots

A bare uniform `o(q)` error in a principal matrix is not enough near a zero
of its determinant: taking a square root can enlarge it to order
`sqrt(|q|)`. The shared root and one spatial derivative are essential.

For every `q` both effective and original determinants vanish at the same
fixed physical root, by the N03 germ and (8). Their difference is `o(q)`
in `C^1` by (7). Writing `x` for inward distance to the root, the integral
Taylor formula therefore factors their difference as `x o(q)`, uniformly
with angular derivatives. Simplicity of `w'` gives

\[
 b_0^2-a_0c_0=x\,k_0(x),\qquad k_0>0
\]

on a sufficiently small fixed endpoint collar. The divided factors remain
positive for small `q`; square root and division by the uniformly positive
`a_eff` are smooth operations on these factors. Consequently the difference
of the two characteristic speeds is `sqrt(x)o(q)` on that collar. Away
from the endpoints ordinary smooth coefficient calculus applies.

Together with `d=b/a`, this gives the uniform coefficient first variations
needed in the integral form of the characteristic ODE, including at the
roots. Periodicity and bounded angular derivatives give a uniform angular
Lipschitz bound. The usual integral-equation comparison and Gronwall estimate
then justify differentiation of the endpoint flows and their compositions.
This establishes the required uniform remainder in the next section; a
pointwise speed derivative alone would not establish it.

## 7. A fixed cut contradicts the first loop variation

Let `F_q` now denote the left root-loop holonomy (not the coordinate chart).
At the radial state it is `F_0(θ)=θ+T` by (10). The first variation of each
half-flow integrates the coefficient variations along radial angular
translations. Thus the reference-height part is a linear combination of
`cos(2θ)` and `sin(2θ)`, while the radial perturbation has mean

\[
 \kappa=2\int_a^c(-\delta\omega f')\,dr=-2\delta\ne0.
\]

The chart-control correction in Section 3 contributes nothing to the
original coefficients, and the effective-operator correction is `o(q)`
by Sections 4 and 6. Consequently there are real `A,B` such that

\[
 F_q(\theta)=\theta+T+
     q\bigl(\kappa+A\cos(2\theta)+B\sin(2\theta)\bigr)+o(q), \tag{11}
\]

uniformly in `θ`. The sign of `κ` changes if the opposite loop convention
is chosen; its nonvanishing does not.

The exact `RadialReturnMargins` clause applies to **every**
`NegativeRadialComponent D a b`, hence to this one. It supplies
`QuadraticIrrational (T/π)`. In particular, `sin T≠0`. This is stronger
than the nonresonance needed to remove the single oscillatory mode in (11).

Put `d=cos(2T)−1`, `s=sin(2T)`, and
`Δ=d²+s²=4 sin²T>0`. The periodic function

\[
 g(\theta)=\frac{-Ad+Bs}{\Delta}\cos(2\theta)
          +\frac{-As-Bd}{\Delta}\sin(2\theta)
\]

satisfies

\[
 g(\theta+T)-g(\theta)=-A\cos(2\theta)-B\sin(2\theta).
\]

Set `H_q(θ)=θ+q g(θ)`. Its displacement from the identity is bounded.
Equation (11), the displayed cohomological identity, and the bounded
derivative of `g` give

\[
 H_q(F_q(\theta))-H_q(\theta)=T+q\kappa+o(q)
\]

uniformly in `θ`. Telescoping this estimate along iterates shows that their
average displacement lies between `T+qκ−o(|q|)` and `T+qκ+o(|q|)`.
Section 5, however, gives an exact boundary-chart conjugacy to translation
by `T`, so that average displacement equals `T`. Hence

\[
 |q\kappa|\le o(|q|),
\]

contradicting `κ≠0` for sufficiently small nonzero `q`.

This last step does not assume a general differentiability theorem for
rotation numbers. It does not even require using `H_q` as an invertible
conjugacy: bounded displacement and orbit telescoping suffice. The helper
`N04bRotationBounds` isolates the corresponding degree-one-lift estimate.
The preexisting `N04bFourierCorrector`, `N04bRotationVariation`, and
`N04bRotationVariationBound` interfaces provide the physical-period
formulation; their revised bounded-corrector application still needs its
own successful CI check.

### Why the usual changes of presentation do not remove this issue

- The perturbation is chosen after an arbitrary proposed cut is fixed, so
  the argument concerns every possible existential choice of atlas.
- Shrinking the positive neighborhood does not remove it: both the radial
  bump and the odd chart-state direction can be scaled arbitrarily small.
- The N03 operator cannot cancel this first-order half-travel change along
  the chosen path, because its actual error is `o(q)` on all the probes.
- Values assigned to the stored inverse at a canonical boundary do not
  change the interior characteristic holonomy or the closed forward chart.
- A different valid canonical chart only conjugates the same physical
  loop. It does not change its average displacement.
- No exact zero-return solution or general rotation-number differentiability
  theorem is required.
- Allowing only a state-dependent radial cut still fails to represent the
  manuscript's general angle-dependent travel level.

## 8. Minimal coherent statement repair

The conflict is the demand that the artificial physical cut remain a fixed
radial circle while the canonical halves and their operators are fixed.
The manuscript preserves the canonical geometry by allowing precisely that
physical cut to move. The corresponding repair should make the domain an
actual state-dependent geometric object, rather than assume the final
normal form as a new hypothesis.

Concretely, the negative halves in the intended construction are

\[
 \Omega_{z,m,L}
   =\{p:a_m<p_1<b_m,\ 0<\sigma_{z,m}(p)<T_m/2\},
\]
\[
 \Omega_{z,m,R}
   =\{p:a_m<p_1<b_m,\ T_m/2<\sigma_{z,m}(p)<T_m\}.
\]

Their common cut is `Γ_z,m(θ)=X_z,m(T_m/2,θ)`, where `X` is the genuine
inverse of the actual travel chart.

1. Give the physical piece domain a state argument, for example an actual
   `physicalDomain z m : Set PolarPoint`, and define
   `physicalPieceOpen S K z m` from it. It can equivalently be the image of
   an explicitly constructed closed/open half-cylinder under the inverse
   travel chart. Reference radial endpoint metadata may remain, but must
   no longer define all perturbed negative domains.
2. For a negative pair, retain the genuine fixed root circles `C.left m`
   and `C.right m`. Specify a common physical cut parametrization
   `cutPoint z m θ = X_z(T_m/2,θ)` and the two domains bounded by that
   curve and the roots. A periodic embedded curve is sufficient; do not
   assume a radial-graph representation without proving its transversality.
3. Make the Part A sign conditions, the almost-everywhere partition, the
   chart/inverse identities, and the smooth nondegenerate boundary
   extensions refer to these actual domains for each state. The partition
   is now a partition of the physical cylinder, not merely of its radial
   axis. Keep periodicity, reflection symmetry, positivity, and
   normalization on the designated region.
4. In Part B replace the equality of two constant physical cut radii by
   their equality to the same physical cut curve, with the real chart and
   height boundary germs at that curve. Keep both canonical intervals
   `(0,R_m)`, with `R_m=(3T_m/4)^(2/3)`, and keep the exact transmission
   coefficient `−1/(2R_m)` and the actual Tricomi operator conclusion.
5. Preserve the definitions of `canonicalHeight`, `canonicalSource`, and
   `canonicalOperator` as the genuine pullbacks and conjugated physical
   divergence expression. No freely assigned operator may replace them.
6. Update the matching clauses of `N04Properties`, not only its blueprint
   fragments. In particular its source pairing must integrate over
   `physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc 0 π)` on the physical side.
   The canonical integral and its genuine Jacobian transformation remain.
7. Update `Blueprint/Assembly.lean` together with the definitions so that
   `N04_of_nodes` assembles exactly the repaired conjunction. Audit
   `N04a`, `N04Coordinates`, and every use of `physicalPieceOpen` for the
   new state argument. A reference affine atlas can use constant domains;
   it does not supply the negative normal-form conclusion at nearby states.

The root regularity, construction of the travel diffeomorphism, boundary
transmission, source-pairing change of variables, and quantitative estimates
remain mathematical proof obligations after this repair. Changing the domain
interface does not prove them. In particular, the repair must not turn the
desired normal form or the desired cut pullback into an assumed structure
field with no construction.

This audit does not edit the shared statement files, the assembly, or the
lead-owned status ledger. Any agreed repair must be coordinated and checked
as one consistent change.

## 9. Formal obligation ledger

The argument separates explicit calculations from the remaining analytic
and topological work. The following items must be proved against the actual
frozen predicates before claiming a formal contradiction or revising the
task's completion status.

| Obligation | Precise content | Current role |
| --- | --- | --- |
| Actual coefficient derivatives | Derive (2) for `b/a` and `sqrt(b²−ac)/a`, with real neighborhood admissibility. | Isolated in new optical-variation helper sources; CI must validate them. |
| Balanced physical perturbation | Construct compact radial `f` satisfying (1), represent it in the actual height space, and place `x_δ` in the common neighborhood. | Balanced-test and height helper sources cover the scalar construction; representation and neighborhood transport still need integration. |
| Actual return derivative | Differentiate the N01 flow and N02 inverse/right-chart formula, identify all components of `ρ`, and prove evenness and zero mean. | Mathematical flow calculation described above; not a completed Lean theorem here. |
| Joint path derivative | Apply the actual N02 derivative and odd inverse on the affine sector path to obtain (3) in the projective topology. | Requires explicit state/sector and `chartIncrement` transport. |
| Uniform source-to-jet control | Bound decoded compact `C^j` norms by actual physical source seminorms; use error linearity to prove (5). | Essential analytic bridge; pointwise continuity is insufficient. |
| Effective principal extraction | Localize canonical tests, derive (4), and apply the finite even probes and fixed-factor division in (6). | Avoids any unstated raw-coefficient smoothness; requires formal local operator calculus and division estimates. |
| Boundary topology | Prove boundary values of the forward chart, determinant identity (8), the genuine root identification, and boundary angular diffeomorphisms. | Must use closed forward-chart regularity, not unconstrained inverse boundary values. |
| Closed-interval flow variation | Factor the shared determinant zero, establish uniform angular Lipschitz estimates, and obtain endpoint variation with a uniform remainder. | Necessary to pass from pointwise formulas to (11). |
| Holonomy conjugacy | Transport the actual two characteristic families to the Tricomi strip and prove (9) and (10) as lift identities/invariants. | Does not follow just from naming a normal-form coefficient tuple. |
| Fourier/telescoping bound | Remove the one nonconstant mode and bound the average displacement from (11). | Isolated in `N04bRotationBounds`; its application still needs the actual holonomy and uniform remainder. |
| Universal witness conclusion | Quantify the above over every cumulative witness of `N04bStatement`. | Required because disproving one atlas construction does not refute the existential endpoint. |

The finite Fourier step and the scalar speed variation are substantially
smaller than the analytic bridges. They must not be reported as completion
of the global obstruction. Conversely, the missing bridges are specific:
they do not justify silently treating the fixed physical radial strip as
the manuscript's moving travel half.
