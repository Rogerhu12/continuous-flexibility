# PositiveGeometry: the universal normalization-buffer quantifier

## Finding and scope

The frozen `N04RealizationPositiveGeometryObligation` quantifies over **every**
`N04PositiveNormalizationBuffer`. That qualitative buffer contract permits the
right center of each positive component to approach its right endpoint at an
arbitrary rate. The conclusion nevertheless requires one sampled-`E0` power,
and one derivative loss, uniformly over all components. These requirements are
incompatible: the boundary angular label can vary independently on each
negative component, whereas the chosen positive transport must already be the
identity at the buffer's right center.

The argument below uses only the **first spatial derivative value estimate**
for `.inverseAngleDefect`. It does not rely on estimates for parameter
derivatives, inverse differentiation, a particular Taylor interpolation, or
any proposed construction of `τ`, `σ`, or `Q`.

This note gives an ordinary mathematical refutation of the displayed universal
buffer assertion and records the corresponding source identities. It does not
claim that Lean has checked the complete theorem
`¬ N04RealizationPositiveGeometryObligation`. The new supporting Lean modules
must be compiled and audited separately; the blueprint statement is unchanged.

## The exact contracts involved

In `Analysis/N04RealizationLeadCurrentSplit.lean`, the problematic part is:

```lean
∀ (e : ℕ ≃ N04WholePieceIndex W.D)
  (B : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi)),
∃ (b : ℕ) (ε : ℝ) ...,
  ...
  (∀ z ∈ stateNeighborhood W.S W.C b ε, stateSector W.S z.1 → ∀ i,
    WholePositiveTransportMatching 3 ...
      (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
      (B.centerLeft i) (B.centerRight i) (lower i) (upper i)) ∧
  ...
  ∀ η, ... GeometryData η ... b ε
```

`Analysis/N04PositiveNormalizationBuffer.lean` imposes only the strict order

```text
left < centerLeft < normalizationLeft < normalizationRight < centerRight < right
```

and containment of the prescribed support in the normalization interval. In
particular, it contains no lower bound for `right - centerRight` or for its
canonical-coordinate counterpart.

`WholePositiveTransportMatching.geometry`, in
`Analysis/WholePositiveTransportAssembly.lean`, is a
`WholeComponentTransportGeometry`. Its `middle_germ` field, defined in
`Analysis/EndpointTransportGeometry.lean`, requires

```lean
∀ x ∈ Icc c d, ∀ θ, τ =ᶠ[𝓝 (x, θ)] (id : PolarPoint → PolarPoint)
```

Consequently `τ (d, θ) = (d, θ)` at the selected right center `d`.

`CurrentJetDataOn`, in `Analysis/N04RealizationLeadCurrentData.lean`, requires
one `loss` and, for each `s`, one positive real constant `C` such that on every
positive piece

\[
 \left|\partial_y^i\partial_\theta^j(f_z-f_0)\right|
 \le C E_m^C H_m^{3/4}\,p_{s+\mathrm{loss}}(z),
 \qquad i+j\le s.
\]

Here `p_s` is `parameterGrading`, and `E_m,H_m` are evaluated at the material
sample of the piece. The estimate holds throughout `unitStrip`, whose radial
factor is `(0,1)`.

## 1. The actual endpoint label supplies an independent perturbation

Fix a retained start `W`, its choices `X`, and an allowed reference family
`Y,H`. Write a positive component as `(l_i,r_i)`.

Every endpoint of the retained reference is interior; this is a field of
`N04RealizationStart` (`roots`). Therefore `X.src i true` cannot be its `none`
branch. For some negative component index `m_i`, its subtype certificate says

\[
r_i=C.\mathrm{left}(m_i).
\]

The definition of `n04PositiveSourceMap` in
`Analysis/WholePositiveEndpointFields.lean` then selects the **left** half of
that negative component. The theorem
`n04Realization_actualRoot_currentPoint_eq` in
`Analysis/N04RealizationRootBoundaryPoint.lean`, with negative-side selector
`false`, identifies its value at the endpoint as

\[
 F_{z,i}(r_i,\theta)
   =\bigl(r_i,h_{z,m_i}^{-1}(\theta)\bigr),
 \qquad
 h_{z,m}(\theta)=\operatorname{stateLeftChart}(S,z,m,\theta).
\]

The latter definition is literal (`Statements/Nonlinear.lean`):

\[
h_{z,m}(\theta)=\theta+\operatorname{decode}(z.\mathrm{chart})_m(\theta).
\]

For each chosen component, let `v_i` be a chart-only sector direction whose
decoded chart displacement is `sin(2θ)` in slot `m_i` and zero in every other
slot. This is a permitted direction, not an additional hypothesis:

* `circleSingleComponentField_member` in
  `Analysis/CircleSingleComponent.lean` proves membership for every smooth
  π-periodic single-component field.
* The surjectivity clause of `IsCircleModel` in `Statements/Analysis.lean`
  realizes that field in the same existing circle space; `W.hS` supplies this
  exact circle-model certificate.
* The sine is odd, and the other circle component is zero, so the direction
  lies in the actual `stateSectorSubmodule`.

At the reference state all chart displacements are zero. Along the state
`t v_i`, the selected left label is exactly

\[
h_{t,i}(\theta)=\theta+t\sin(2\theta).
\]

Choose `t>0` small enough that `t v_i` is in whatever neighborhood the proposed
conclusion supplies, and also `t<1/4`. Then `h_{t,i}` is strictly increasing.
With

\[
\theta_0=\pi/4,\qquad \theta_t=\theta_0+t,
\]

we have `h_{t,i}(θ₀)=θ_t`, hence `h_{t,i}^{-1}(θ_t)=θ₀` exactly. This avoids
differentiating an inverse with respect to the state.

## 2. The positive inverse atom has two forced values

The theorem `n04WholeReferenceGaugeAtlasData_positive_fields` in
`Analysis/WholeReferenceGaugeAtlasData.lean` gives, on the positive piece:

\[
 V.\mathrm{left}=0,\quad V.\mathrm{right}=1,\quad
 V.\mathrm{inverseChart}_z=\tau_{z,i}\circ
          \bigl(Y_i^{-1},\mathrm{id}\bigr).
\]

Thus the canonical unit coordinate is already `y`; there is no additional
component-dependent scaling in `.inverseAngleDefect`. From its definition in
`Statements/Nonlinear.lean`, its angular slice is

\[
 A_{t,i}(y)=
 \bigl[\tau_{t v_i,i}(Y_i^{-1}(y),\theta_t)\bigr]_2-\theta_t.
\]

The reference value of this atom is identically zero because `τ_ref=id`.
The endpoint reference geometry gives `Y_i(r_i)=1`. The order-zero coordinate
matching condition and the endpoint calculation in §1 give

\[
A_{t,i}(1)=-t.
\]

Let `d_i=B.centerRight i` and `q_i=Y_i(d_i)`. The actual middle germ forces

\[
A_{t,i}(q_i)=0,\qquad 0<q_i<1.
\]

All functions here are smooth globally in the spatial variables by the
matching geometry and the reference geometry. Hence their values at `y=1`
are genuine continuous boundary values. The fact that `unitStrip` itself is
open does not remove the obstruction: the mean value theorem uses derivatives
only for `q_i<y<1`.

## 3. A necessary lower bound on every right canonical collar

Put

\[
\Delta_i=1-Y_i(d_i)>0,\quad
E_i=W.U.E0(W.U.sample(X.cell(i))),\quad
H_i=W.U.H(W.U.sample(X.cell(i))).
\]

Use the value estimate in `CurrentJetDataOn` with `s=1`, `i=1`, `j=0`.
Write its loss as `ℓ` and its constant as `C>0`. The estimate, the two forced
values above, and the mean value theorem imply

\[
t\le\Delta_i C E_i^C H_i^{3/4}\,p_{1+\ell}(t v_i).
\]

Every grading is a seminorm, so `p_{1+ℓ}(t v_i)=t p_{1+ℓ}(v_i)`. Cancelling
the positive `t` gives the necessary condition

\[
\boxed{1\le\Delta_i C E_i^C H_i^{3/4}\,p_{1+\ell}(v_i).}\tag{*}
\]

This cancellation explains why raising the neighborhood's base index or
shrinking its positive radius cannot repair the universal buffer assertion.
The amplitude `t` may be chosen separately for each component after that
neighborhood is known, and then disappears from (*).

The auxiliary column does not affect this argument. One may take `η=0` in
the asserted `∀ η`: replacement preserves the circle space, its grading,
the reference state, and the geometric chart/inverse fields.

## 4. A valid buffer that violates every possible loss and constant

There are infinitely many distinct positive components of the retained
reference. Concretely,
`retainedReference_positive_gap_is_component` in
`Analysis/RetainedMorsePositiveGapComponents.lean` supplies the right-tail
gap for each index `S₀.chain.index+n`. Their right endpoints are the left
turns of successive Morse models, which are strictly increasing by
`morseRealization_turning_component_order` in
`Analysis/MorseRealizationComponentOrder.lean`. Denote these distinct
components by `i_n`, `n∈ℕ`.

Choose the single-component direction `v_n` from §1 for each `i_n`, and put

\[
K_n=1+\sum_{j=0}^{n+1}p_j(v_n)>0,
\qquad
\delta_n=
\frac{1}{(n+1)\bigl(1+E_n^{n+1}H_n^{3/4}K_n\bigr)}>0.
\]

These are choices made before any proposed realization, neighborhood, loss,
or estimate constant. The material floor gives `E_n≥1`; all displayed
weights are finite and nonnegative.

Start from any allowed buffer `B₀`. Keep `centerLeft`, `normalizationLeft`,
and `normalizationRight` exactly unchanged. Move only `centerRight i_n`
toward `r_{i_n}`, far enough that

\[
0<\Delta_n=1-Y_{i_n}(B.centerRight(i_n))<\delta_n.
\]

This is possible by continuity and `Y_i(r_i)=1`. It preserves all strict
ordering conditions, and the support condition is literally unchanged.
There is no need to discard finitely many support-containing components.
Use any positive gap budget on the remaining components.

Now suppose the asserted realization exists and take its loss `ℓ` and
constant `C` for `s=1`. Choose `n` with

\[
n+1>C,\qquad n+1\ge 1+\ell.
\]

Then `p_{1+ℓ}(v_n)≤K_n` and `E_n^C≤E_n^{n+1}`. The right side of (*) is
strictly less than

\[
\frac{C}{n+1}
\frac{E_n^{n+1}H_n^{3/4}K_n}
     {1+E_n^{n+1}H_n^{3/4}K_n}
\le\frac{C}{n+1}<1,
\]

contradicting (*). This rules out every possible positive transport family,
not merely the existing family selected by the qualitative interpolation
theorem.

## Supporting Lean work and remaining verification boundary

`Analysis/N04PositiveGeometryBufferFreedom.lean` contains proofs of:

1. smoothness of the scalar coordinate in a cylindrical range certificate;
2. `Y(right)=1` from the existing two closed range conditions and inverse;
3. existence of an interior right center with any positive canonical gap
   budget;
4. construction of the actual `N04PositiveNormalizationBuffer` with that
   budget while preserving the normalization intervals and support.

At the time this note was written these declarations had been written but
not yet compiled in the local environment. CI is the authority for their
compilation and axiom audit. The mean-value/diagonal obstruction and the
actual endpoint/atom identities are being supplied in separate, independently
checkable modules. Until those modules are assembled into a theorem with
the exact negated frozen statement, the distinction remains: the argument
above is a mathematical statement audit, while the repository's original
positive-geometry blueprint is still open.

## Consequence for the intended proof

The manuscript does not ask for this arbitrary-buffer assertion. In
`paper/flexible-surface-readable/07-fixed-geometry.tex`, the proof of the
positive reference-chart lemma selects collars with coefficient-power costs;
the proof of the current-jets lemma then reuses cutoffs that preserve those
costs. A buffer chosen independently and arbitrarily close to every endpoint
does not satisfy that quantitative premise.

A repair must retain a quantitative collar choice in the assembly, for
example by choosing a controlled buffer existentially, or by requiring an
appropriate material lower bound as part of the supplied buffer certificate.
No frozen statement has been edited here. The common task rules reserve that
repair, including its effect on the parent assembly, to the lead.

There is a separate issue to check during that repair:
`N04PositiveReferenceFamily` itself records qualitative geometry and only
the endpoint jets through order four, not uniform material bounds on the
reference family. The universal-buffer contradiction above already suffices
and does not depend on resolving this additional quantifier issue.
