# N04b: audit of the fixed physical cut

## Status and scope

This audit concerns the exact existential statement `N04bStatement` at main
`7393d676930e9b92bfe5a4defa8a79d6f03db323`. It does not criticize the arbitrary
choice of atlas supplied by N04a: N04b is allowed to choose all its witnesses
again. The argument below starts with an arbitrary proposed N04b witness.

The calculation identifies a candidate contradiction between a fixed physical
cut, a fixed common canonical half-radius, and the genuine nonlinear operator
identity. It uses radial height variations available in every stipulated
physical space. It does not require the existence of a nonlinear zero-return
solution, and it does not use the values of the totalized inverse chart at a
canonical boundary.

**This is a mathematical audit, not a Lean proof of `¬ N04bStatement`.**
No frozen statement has been changed on the strength of this document.
The principal-field extraction, full endpoint flow variation, and the
half-holonomy argument must be independently reviewed and then proved as
actual lemmas before a formal contradiction is claimed. The last section
lists these obligations separately from the calculations and source facts
already checked.

## 1. The frozen requirements involved

The data in `Statements/Nonlinear.lean` have

~~~lean
physicalLeft : ℕ → ℝ
physicalRight : ℕ → ℝ
cutRadius : ℕ → ℝ

def physicalPieceOpen (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : Set PolarPoint :=
  Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ univ
~~~

The first conjunct of `N04PartB` includes, for every negative component index
`m`, the exact clauses

~~~lean
K.physicalLeft (K.cutPair m).1 = C.left m ∧
K.physicalRight (K.cutPair m).2 = C.right m ∧
K.physicalRight (K.cutPair m).1 =
  K.physicalLeft (K.cutPair m).2 ∧
0 < K.cutRadius m ∧
K.left (K.cutPair m).1 = 0 ∧
K.left (K.cutPair m).2 = 0 ∧
K.right (K.cutPair m).1 = K.cutRadius m ∧
K.right (K.cutPair m).2 = K.cutRadius m
~~~

Both pieces have `positive = false`. Part A gives strict physical interval
lengths. Consequently, writing

\[
 \ell=C.left(m),\quad r=C.right(m),\quad
 c=K.physicalRight((K.cutPair\,m).1),\quad R=K.cutRadius(m),
\]

one has \(\ell<c<r\), \(R>0\), and two physical strips
\((\ell,c)\times\mathbb R\) and \((c,r)\times\mathbb R\), both mapped onto
\((0,R)\times\mathbb R\). Neither \(c\) nor \(R\) depends on the state.

Part A also gives the actual smooth forward chart and height, nonzero
Jacobian and positive height at every point of the **closed** physical
piece, together with an actual smooth inverse on the open pieces and
angular lift periodicity by \(\pi\).

The operator and negative-coefficient conjuncts of Part B require

~~~lean
canonicalOperator S K L z m W p =
  divergenceOperator (K.coefficients z m) W p +
    K.potential z m p * W p

(K.coefficients z m).a p = 1 ∧
(K.coefficients z m).b p = 0 ∧
(K.coefficients z m).c p = -p.1
~~~

on a negative canonical piece, for every globally smooth \(W\). Hence the
actual transformed operator on each half is
\(\partial_\xi^2-\xi\partial_\varphi^2+V\).

These conditions already impose the half-return restriction below. The
cut-transmission conjunct is not needed for the proposed contradiction.

## 2. Reference facts that are genuinely available

Fix any component \(m\); taking \(m=0\) is enough. Put \(w=D.w\) and

\[
 v_0(s)=\sqrt{-\frac{w'(s)}{s\,w(s)}},\qquad
 t(s)=\int_\ell^s v_0(x)\,dx,\qquad T=t(r)=C.travel(m).
\]

The N01 control geometry gives positive \(w\), \(\ell>0\),
\(w'<0\) on \((\ell,r)\), simple zeros of \(w'\) at both endpoints, and the
displayed formula for \(C.travel\). Thus \(v_0>0\) inside the component,
\(v_0\) tends to zero at both endpoints, and it has the usual square-root
factor at each simple root.

There is also an explicit nonresonance hypothesis. In the pinned source,

~~~lean
def QuadraticIrrational (t : ℝ) : Prop :=
  Irrational t ∧
    ∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * t ^ 2 + b * t + c = 0
~~~

and `RadialReturnMargins` requires

~~~lean
∀ l h, NegativeRadialComponent D l h →
  QuadraticIrrational (radialTravel D l h / Real.pi) ∧ ...
~~~

It is the third conjunct of `IsRadialReference`. The control component is
a `NegativeRadialComponent`, and its travel is that same radial integral.
Therefore \(T/\pi\) is irrational, in particular \(e^{2iT}\ne1\).
This fact does not have to be inferred from the N02 inverse.

The reference state has height
\(u_*(s,\theta)=\phi(s)\cos(2\theta)\) and zero metric, control, and chart
increments. At \(q=0\), with those other increments still zero, the actual
coefficient field is

\[
 A_0(s)=\begin{pmatrix}w(s)&0\\0&w'(s)/s\end{pmatrix}.
\]

It is independent of the height-state variable. The ordinary minus flow is
\(\theta\mapsto\theta-t(s)\). Its inverse return and the odd right chart
therefore give zero return residual. This remains true at \(q=0\) if
\(u_*\) is replaced by any other height sufficiently near \(u_*\).

## 3. Work with the effective smooth operator, not unsupported regularity of L

N03 does not explicitly state smoothness of the functions stored in
`L.coefficients`. The total Fréchet derivative in Lean is zero at a
nondifferentiable point, so it would be unsafe to assume ordinary
product rules for these fields. The following route avoids that assumption.

On one physical half, write \(F\) for its actual forward chart, \(G\) for
the interior inverse, and \(h>0\) for its height. For any physical smooth
test function \(u\), the local canonical function
\((u/h)\circ G\) is smooth. A compact cutoff extends its germ near an
interior point to a globally smooth \(W\), to which Part B applies.
Thus the **actual action** of \(\operatorname{div}L\nabla\) is equal there
to the pullback of the genuine smooth Tricomi operator.

The principal matrix of that actual pullback is

\[
 B=\frac{|\det DF|}{h^2}\,
       (DF)^{-1}
       \begin{pmatrix}1&0\\0&-\xi\end{pmatrix}
       (DF)^{-T},\qquad \xi=F^1.
 \tag{3.1}
\]

This formula uses only derivatives of the known smooth chart and height.
It is smooth in the physical variables and extends to the closed physical
half at every finite derivative order. In particular,

\[
 \det B=-\frac{\xi}{h^4}. \tag{3.2}
\]

The possibly unspecified potential causes no difficulty: the actual
divergence kills the constant function. Applying Part B locally to
\((1/h)\circ G\) identifies \(V\) with a smooth expression and cancels
the zeroth-order term in the physical pullback. The inverse coordinate
and gauge calculation then identifies the actual physical action with
\(\operatorname{div}(B\nabla)\). This is a reverse use of the genuine
coordinate-divergence identity, not an identification of arbitrary
stored values of \(L.b,L.c\).

N03 gives, for every physical height test \(\eta\),

\[
 \operatorname{div}(A_{\rm orig}\nabla\eta)
 -\operatorname{div}(B\nabla\eta)
 =\mathcal E_z(R_z)\eta. \tag{3.3}
\]

The error is linear in \(R_z\), linear in \(\eta\), and jointly smooth tame
in the stipulated projective spaces.

### Even test functions suffice to extract B

The physical height space contains every smooth, even, \(\pi\)-periodic
function with compact radial support; no zero angular mean is required
by `HeightMember`. Its decoder is surjective onto that class.

Choose one radial cutoff equal to one on a neighborhood of
\([\ell,r]\). Radial polynomial tests \(1,s,s^2\), multiplied by that
cutoff, extract \(B_{11}\). Products with \(\cos(2\theta)\) and
\(\cos(4\theta)\) extract the other entries by the carré-du-champ identity

\[
 \tfrac12\big(P(fg)-fP(g)-gP(f)\big)
   = \nabla f^T B\,\nabla g
\]

for the actual zero-potential divergence operator \(P\).
In particular the mixed probe gives a fixed multiple of
\(B_{12}\sin(2\theta)\), and the angular square probe gives a fixed
multiple of \(B_{22}\sin^2(2\theta)\).
The same formulas apply to \(A_{\rm orig}\).

Away from the reflection axes this identifies all entries directly.
Near an axis, ordinary smooth division by the fixed sine factor,
using its vanishing jets, gives the same unique extension. For uniform
bounds one loses one angular derivative for the mixed probe and two for
the angular square probe. The forward-chart reflection identities give
the expected odd/even parity; they also identify the values on the axes
by continuity. This handles the restriction to even physical tests
without assuming access to an odd height state.

Consequently, if \(R_{z(q)}=o(q)\) in every circle seminorm, (3.3) and the
smooth tame error imply

\[
 B(q)-A_{\rm orig}(q)=o(q)
 \quad\hbox{in every compact physical }C^k\hbox{ norm}. \tag{3.4}
\]

The projective physical norm equalities and compact Sobolev estimates
justify passage from source seminorms to these compact jet norms.
The same probes identify the principal field across the fixed cut:
their source outputs are smooth on the whole annulus. Thus the two
half formulas do not introduce an unproved interface regularity
assumption. No state smoothness of the chosen \(F,h\) has been assumed;
the actual principal field gets its parameter dependence from (3.3).

At a turning root, N03 gives germs equal to the original \(b,c\), and
the \(a\) field is equal everywhere. Hence the effective field agrees
with the original on a neighborhood of that root for each state.
The difference in (3.4) is flat at each fixed root. Dividing by the
fixed endpoint-distance factors, with the corresponding finite
derivative loss, preserves its \(o(q)\) property.

## 4. A canonical half fixes a characteristic round trip

The stored inverse need not be continuous at \((R,\theta)\). That gap
does not defeat this argument, since only the forward chart and its
genuine local inverse are used.

For a physical endpoint \(p\), continuity of \(F\) and continuity of
the specified inverse on the canonical **interior** imply that \(F(p)\)
lies on the canonical boundary. Indeed, if it were an interior point,
apply that continuous inverse to a sequence of interior physical
points tending to \(p\); its limit would be \(p\), contradicting the
requirement that the inverse maps the canonical interior into the
physical interior.

This exact argument is already proved on PR #18 by
`canonicalChart_endpoint_radial_eq_boundary` in
`Analysis/CanonicalBoundaryImage.lean`. The genuine endpoint local
inverse is provided by
`canonicalChart_exists_smooth_endpointInverse` in
`Analysis/CanonicalEndpointInverse.lean`.

At a root, (3.2) and the N03 root germ force the image coordinate to
be \(\xi=0\), because the original determinant is zero there and
\(h>0\). The other physical boundary therefore maps to \(\xi=R\).
For the latter assertion, use interior surjectivity and compactness
modulo the angular period: a sequence with canonical radii tending
to \(R\) has a physical subsequence in the closed cylinder, and its
limit cannot be interior or on the already identified root boundary.

The boundary angular maps are degree-one circle diffeomorphisms.
Their derivative cannot vanish, since the radial coordinate is
constant along the boundary and the actual Jacobian is nonzero;
the lift condition fixes the positive degree. The local inverse
function theorem supplies their genuine inverse. No value of
`K.inverseChart` at the canonical boundary is used.

The two genuine characteristic first integrals of
\(\partial_\xi^2-\xi\partial_\varphi^2\) are

\[
 \varphi-\tfrac23\xi^{3/2},\qquad
 \varphi+\tfrac23\xi^{3/2}.
\]

Put \(H=\tfrac23R^{3/2}\). Following one family from the root to the
cut and returning along the other gives a physical circle lift
conjugate to the translation by \(-2H\). The height factor and the
potential do not affect the principal characteristics.

At \(q=0\), (3.3) has zero error. Hence \(B=A_0\), the left physical
half has travel \(t(c)\), and the right half has travel \(T-t(c)\).
Their common \(R\) forces

\[
 t(c)=H=T-t(c),\qquad t(c)=T/2,\qquad 2H=T. \tag{4.1}
\]

For every nearby state, each canonical half still has the same \(R\).
Its actual half-round-trip map must therefore remain conjugate to
the **same** translation by \(-T\).

This conclusion uses the closed forward-chart nondegeneracy and the
actual operator identity. It does not assume that the manuscript's
chosen travel chart is the only possible chart, and it does not use
the cut-transmission values of the totalized inverse.

## 5. A height variation that preserves full travel to first order

For \(Z=Z_0+q u\), with \(Z_0'=w\), hold the metric and control states
fixed at zero. Write \(E=1+w^2\). From the actual frozen coefficients,

\[
 D=1-2qwu_s+O(q^2),\quad
 Q=w+q\left(u_s+\frac{E}{s}u_{\theta\theta}\right),\quad
 a=Q D^{-3/2}.
\]

The proved original determinant identity is

\[
 a c-b^2=\frac{w w'}{sD^2}.
\]

Therefore the half-width of the two characteristic speeds is exactly

\[
 v=\frac{\sqrt{b^2-ac}}a
   =\frac{\sqrt{-w w'/s}\sqrt D}{Q},
\]

and its first derivative at zero is

\[
 \dot v=-v_0\,\frac{1+w^2}{w}
          \left(u_s+\frac{u_{\theta\theta}}s\right). \tag{5.1}
\]

The drift derivative is

\[
 \dot d
 =-\frac{1+w^2}{w}
     \left(\frac{u_{s\theta}}s-\frac{u_\theta}{s^2}\right). \tag{5.2}
\]

For the reference height \(\phi(s)\cos(2\theta)\), these derivatives
contain only angular frequency two. For a radial added height \(f(s)\),
the added drift derivative is zero and the added speed derivative is

\[
 -\omega(s)f'(s),\qquad
 \omega(s)=v_0(s)\frac{1+w(s)^2}{w(s)}. \tag{5.3}
\]

The smooth positive function \(\omega\) in the open component tends to
zero at both roots. It cannot be constant on either half.
Choose compact smooth bumps \(f_L,f_R\), supported strictly inside
\((\ell,c)\) and \((c,r)\), respectively, such that

\[
 I_L=-\int_\ell^c\omega f_L'\ne0,\qquad
 I_R=-\int_c^r\omega f_R'\ne0.
\]

For example, integration by parts reduces the first functional to
\(\int\omega'f_L\); choose a nonnegative bump where \(\omega'\) has a
nonzero fixed sign. The right half is identical.

Set

\[
 f=f_L-\frac{I_L}{I_R}f_R.
\]

Then

\[
 -\int_\ell^r\omega f'=0,\qquad
 -\int_\ell^c\omega f'=I_L\ne0. \tag{5.4}
\]

The radial function \(f(s)\), constant in angle and extended by zero,
is a legitimate `HeightMember`: its radial support is compactly
inside the annulus, and all material weights and coordinate factors
are smooth and bounded there. Surjectivity of the physical decoder
realizes it as an actual height state. Choose a nonzero small
\(\delta\), so that

\[
 u_\delta=u_*+\delta f
\]

lies inside the given low-order neighborhood. This choice is made
after the proposed fixed cut \(c\) is known, so it applies to every
possible existential choice of the cut.

### Cancel the full return derivative, not the half derivative

At the base state with height \(u_\delta\), zero metric/control/chart
increments and \(q=0\), the return residual is zero. N02's actual smooth
tame residual supplies its derivative \(\rho\) in the actual circle space
in the \(q\) direction.

The linearized ordinary flow at a radial reference preserves each
angular Fourier frequency. The \(u_*\) part contributes only frequency
two. The radial part contributes a constant proportional to the full
integral in (5.4), which is zero. The definition of the return residual
takes its even part; the varying right-chart inverse has no first-order
effect on an outer residual whose value at zero is identically zero.
Thus \(\rho\) is an even zero-mean circle element at every component.
Its weighted membership is supplied by the genuine N02 derivative,
not by an unsupported estimate of a formal sequence of Fourier coefficients.

Take

\[
 v=-R.inverse(\rho)
\]

and vary the odd chart state by \(qv\), holding \(u_\delta\), the metric
state, and the control state fixed. The state remains in `stateSector\):
the control is constant zero and \(v\) is odd by N02. For small \(q\)
it remains in the same positive-radius state neighborhood.

At zero chart increment, `R.chartIncrement` is the identity (by its
decoded formula and decoder injectivity). The N02 derivative in this
chart direction is \(R.linearPart(v)=-\rho\), since its error is linear
in the zero base residual. Joint smoothness therefore gives

\[
 R_{z(q)}=o(q) \tag{5.5}
\]

in every circle seminorm.

This step requires no nonlinear implicit-function theorem and no
nonlinear curve with exactly zero residual. The genuine first derivative
and N03's smooth linear error are enough.

### Transfer the first variation to the effective operator

Equations (3.3)--(3.4) and (5.5) show that the effective principal field
has the same first variation as the original one. It remains positive
in its radial principal entry on the compact component for small \(q\).
Its determinant has the same simple endpoint factors: the original
determinant has them, and the error is flat at the roots and \(o(q)\)
after division by those fixed factors.

Thus the actual characteristic speeds have the original first
variation, uniformly in the integrable endpoint coordinates. Ordinary
ODE variation on the full closed half applies after the usual root
time substitution. This is the endpoint-flow bridge that must be
proved explicitly; a result only on compact subintervals would not suffice.

The actual left half-round-trip lift consequently has the expansion

\[
 F_q(\theta)=\theta-T+
 q\big(g_0+g_c\cos(2\theta)+g_s\sin(2\theta)\big)+o(q)
 \tag{5.6}
\]

uniformly in \(\theta\). For the convention “minus out, plus back,”

\[
 g_0=-2\delta I_L\ne0. \tag{5.7}
\]

The two passages through the half add the radial travel variation.
The reference-height contribution remains frequency two under the
reference translations. The added chart state does not enter the
original physical coefficients at all; it was used only to make the
N03 correction have zero first derivative.

## 6. The finite Fourier contradiction is elementary

Because \(e^{2iT}\ne1\), a trigonometric polynomial \(k\) of frequency two
solves the finite cohomological equation that removes the oscillatory
part of (5.6). The lift

\[
 H_q(\theta)=\theta+qk(\theta)
\]

is a degree-one circle diffeomorphism for small \(q\). Its conjugated
round-trip map satisfies

\[
 H_q F_q H_q^{-1}(\theta)=\theta-T+qg_0+o(q)
 \tag{6.1}
\]

uniformly in \(\theta\).

Choose the sign of \(q\) so that \(qg_0>0\), and then make \(|q|\) small.
Every displacement in (6.1) is strictly greater than
\(-T+|qg_0|/2\). Iteration gives an excess of at least
\(n|qg_0|/2\) over the translation by \(-nT\).

But section 4 says that this same map is conjugate to translation by
\(-T\). Every \(\pi\)-periodic degree-one conjugating lift differs from
the identity by a bounded function. Its iterates can therefore differ
from \(\theta-nT\) by only a bounded amount (for this fixed \(q\)),
contradicting the linearly growing excess.

This does not invoke differentiability of an abstract rotation-number
functional. It needs only the finite Fourier calculation, monotone
iteration, and bounded displacement of a periodic conjugacy.

## 7. Why common shortcuts do not resolve the issue

- The failure of a particular N04a atlas would not refute N04b. The
  variation above is chosen after **arbitrary** N04b witnesses are fixed.
- Changing the return-corrected operator freely is not permitted along
  the constructed path: its N03 error is \(o(q)\), so it cannot cancel
  the nonzero first-order half-travel change.
- It is unnecessary to find an exact nonlinear zero-return state.
- Values assigned to `K.inverseChart` at the canonical cut cannot repair
  the interior half-holonomy restriction. The argument uses the actual
  closed forward chart and its genuine local inverse.
- A second choice of characteristic charts cannot change the invariant:
  it only conjugates the same half-round-trip lift.
- Shrinking the positive neighborhood does not remove the variation.
  The radial bump and the chart-state curve can be scaled arbitrarily small.
- Allowing only a state-dependent **radial** cut would still miss the
  manuscript's general angle-dependent cut. The manuscript uses the
  actual level \(\sigma=T/2\).

## 8. Minimal scientific repair to prepare if the audit is confirmed

The manuscript's construction should retain its actual physical domains:

\[
 \Omega_{z,m,L}
 =\{p:\ell_m<p^1<r_m,\ 0<\sigma_{z,m}(p)<T_m/2\},
\]
\[
 \Omega_{z,m,R}
 =\{p:\ell_m<p^1<r_m,\ T_m/2<\sigma_{z,m}(p)<T_m\}.
\]

Their common boundary is the actual moving cut

\[
 \Gamma_{z,m}(\theta)=X_{z,m}(T_m/2,\theta),
\]

where \(X\) is the genuine inverse of the travel chart. The canonical
half-radius remains fixed:

\[
 R_m=(3T_m/4)^{2/3}.
\]

A suitable statement-layer repair would do the following consistently.

1. Give `CanonicalData` actual state-dependent physical domains and a
   genuine cut curve, or an equivalent representation derived from the
   actual travel chart. Keep canonical intervals fixed. Avoid representing
   a curved physical cut by a pair of constant radial endpoints.
2. Make `physicalPieceOpen` take the state parameter. In Part A, require
   actual open nonempty domains, annular inclusion, sign on the actual
   points, periodic/reflection invariance, and a measure-zero exceptional
   set for their two-dimensional partition. Keep the genuine chart/inverse
   identities and smoothness, positive height, and nonzero Jacobian.
   Apply the closed-piece regularity to the actual physical closure.
3. In Part B replace the fixed radial half-identifications by actual
   decomposition of each negative component into the two domains and
   their common cut. Identify both actual chart traces and actual boundary
   inverses on \(\Gamma_{z,m}\). Keep the same common \(R_m\), the exact
   transmission matrix, the actual canonical operator identity, and the
   negative coefficients \(1,0,-\xi\).
4. In the source-pairing clause integrate over the actual state-dependent
   physical domain. Keep the definitions of `canonicalHeight`,
   `canonicalSource`, and `canonicalOperator` as the actual coordinate
   and height transforms.
5. Carry the same revised Part A/B clauses into `N04Properties`, all three
   N04 stage statements, and the conjunction assembly in
   `Blueprint/Assembly.lean`. Update the N04a construction and the
   N04Coordinates source-pairing/endpoint interfaces accordingly.
   Do not leave two incompatible copies of the canonical parts.
6. Construct the domains from the actual characteristics, prove the
   transmission formula and all operator/estimate conclusions, and
   recheck the complete dependency chain. Do not add the desired Tricomi
   normal form or the final N04 estimate to an upstream hypothesis.

This is a proposed repair, not a completed implementation or permission
to weaken the target. It preserves the manuscript's canonical geometry,
operator, transmission, source pairing, and downstream quantitative
obligations, while correcting which physical sets are being charted.

## 9. Verification ledger and next proof obligations

### Checked directly against the pinned definitions

- The physical halves and their common canonical radius are state-independent.
- Part A has closed forward-chart smoothness and nonzero actual Jacobian.
- Part B quantifies the actual operator identity over every smooth \(W\).
- `IsRadialReference` includes the quadratic irrational travel margin.
- `HeightMember` allows compact radial height perturbations.
- The Sobolev decoder is surjective onto that physical class.
- N02 provides the genuine residual derivative, the chart-direction
  derivative, and an inverse on even zero-mean circle elements.
- N03's error is genuinely linear in both residual and height test and
  jointly smooth tame.
- The first-speed variations (5.1)--(5.3) follow from the displayed exact
  coefficient and determinant formulas.
- PR #18 already proves boundary-image and actual endpoint-local-inverse
  facts without prescribing stored inverse values at the boundary.

### Complete mathematical reductions described above, not yet kernel-checked

1. Reverse the actual canonical operator to a smooth effective physical
   divergence field and prove its determinant formula.
2. Use the compact even probes, including the reflection axes, to obtain
   the compact \(C^k\) version of (3.4) from the projective source error.
3. Prove the closed-strip half-holonomy conjugacy from that effective field.
4. Formalize the compact bump construction and actual height-space realization.
5. Identify the decoded full-return derivative and form the actual sector
   path with residual derivative zero.
6. Carry the first variation through the simple roots on the full half,
   obtaining the uniform expansion (5.6), not merely an interior expansion.
7. Prove the finite trigonometric conjugation and iterate contradiction.

Until these bridges have been independently checked, this audit should be
reported as a concrete obstruction under investigation. It must not be
reported as a Lean-certified refutation, a closed N04b task, or a completed
statement repair.

## Sources

All frozen definitions above were read at
`7393d676930e9b92bfe5a4defa8a79d6f03db323`:

- `src/ContinuousFlexibility/Blueprint/Statements.lean`:
  `N04PartA`, `N04PartB`, `N04aStatement`, `N04bStatement`.
- `src/ContinuousFlexibility/Statements/Nonlinear.lean`:
  physical/canonical data, N01--N03, actual operators.
- `src/ContinuousFlexibility/Statements/Analysis.lean`:
  `HeightMember`, `IsSobolevModel`, `IsPhysicalSpaces`.
- `src/ContinuousFlexibility/Statements/Radial.lean`:
  `QuadraticIrrational`, `RadialReturnMargins`, `IsRadialReference`.
- `src/ContinuousFlexibility/Scalar/Linearization.lean` and
  `Scalar/TypeCorrection.lean`: actual coefficient and determinant formulas.
- `paper/flexible-surface-readable/07-fixed-geometry.tex`, especially
  lines 999--1034 and 1155--1196: genuine travel coordinates, root
  coordinates, and the moving travel-midpoint cut.

The existing boundary-image and endpoint-inverse proofs were read at
PR #18 commit `fe5009423b9ffc766438b51d75377229b1fbc938`.
