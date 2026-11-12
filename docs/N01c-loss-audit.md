# N01c audit: parameter derivative loss

Historical audit, 2026-11-11, with the implemented contract repair recorded below. The quoted uniform-loss clause is the original statement before this branch's repair; it is not the current `OrdinaryFlowFamilyTameBounds`. This note is not a completed N01c proof or its axiom check.

## Verified statement discrepancy

The original `Statements/Nonlinear.lean`, in `N01Properties`, fixed `base loss : ℕ` and `ε : ℝ` before both of its last conjuncts. Before the repair, its flow conjunct was literally:

```lean
(∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m a b p,
  a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
  ∃ J : SmoothDirections (stateNeighborhood S C base ε) (ordinaryFlowFamily S C m a b p),
    ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
      min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base (s + loss) (z - (C.referenceState, 0)) v)
```

Thus the old clause required the same finite loss for every state derivative order `k`. The coefficient conjunct had the same quantifier order, which this branch retains for coefficients. In contrast, the manuscript's `eq:tame-derivative-shape` in `paper/flexible-surface-readable/07-fixed-geometry.tex`, lines 222–231, uses `s+d_k` and explicitly requires independence of the spatial order `s`, not independence of `k`. Proposition 7.8(iii), lines 790–796, invokes this derivative estimate. Lemma `current-geometric-jets`, lines 1619–1627, does the same. Step 5, lines 1700–1710, enumerates a fixed spatial differential cost, then separately discusses state differentiation of the flow equations; it does not remove the additional angular derivatives created by repeated parameter differentiation.

The general `SmoothTameOn` definition in `Statements/Analysis.lean` already had the order `∀ k, ∀ x0 ∈ U, ∃ loss base, ...`. Therefore a theorem proving smooth tameness could not simply be unpacked to obtain that former N01 flow clause. The repaired N01 bound additionally keeps one common base and radius before all derivative orders.

## Exact counterexample for ordinary smooth circle flows

This is a fully explicit counterexample to a *general circle-flow theorem with the frozen quantifier order*. It is not, by itself, a formal counterexample to the existential statement `N01bStatement → N01Statement`, which restricts speeds to the project's nonlinear geometry.

Let the circle be `ℝ / πℤ`. Choose nonnegative smooth functions `α, β : ℝ → ℝ` with compact disjoint time supports, with `supp α ⊂ (0,1)`, `supp β ⊂ (2,3)`, and both integrals equal to 1. For a scalar `a` and a smooth π-periodic vector field `f`, consider

\[
  \dot\theta(t)=a\alpha(t)+\beta(t)f(\theta(t)),\qquad \theta(0)=\theta_0.
\]

Both stages are complete circle flows. If `Fl_f^1` is the time-one autonomous flow of `f`, the time-three endpoint map is exactly

\[
  P(a,f)(\theta_0)=\operatorname{Fl}_f^1(\theta_0+a).
\]

At `f=0`, its derivative in a vector-field direction `h` is

\[
  D_fP(a,0)[h](\theta_0)=h(\theta_0+a).
\]

Indeed, differentiating `Fl_{bh}^1(x)` at `b=0` gives `h(x)` directly from the variational equation, or from the integral equation. Consequently, for every `k ≥ 0`,

\[
  \partial_a^kD_fP(0,0)[h](\theta_0)=h^{(k)}(\theta_0).
\]

Equivalently, the total `(k+1)`st derivative evaluated on `k` copies of `(1,0)` and one copy of `(0,h)` is `h^{(k)}(θ0)`. Subtracting the reference flow leaves this derivative unchanged.

Fix arbitrary candidate low order `b` and loss `d`. Set `L=max(b,d)`. On the product space use the usual grading `p_s(a,f)=|a|+‖f‖_{H^s}`. Choose `k>L` and

\[
  h_N(\theta)=N^{-L}\cos(2N\theta-k\pi/2),\qquad \theta_0=0.
\]

For every `j≤L`, the `H^j` norms of `h_N` are bounded uniformly in positive integer `N`; this follows by differentiating the single Fourier mode. But

\[
  |h_N^{(k)}(0)|=2^kN^{k-L}\longrightarrow\infty.
\]

At the reference point `(a,f)=0`, the one-high-factor expression with high order `s+d=d` and `s=0`, evaluated on the directions above, is a fixed finite linear combination of `‖h_N‖_{H^b}` and `‖h_N‖_{H^d}`, hence uniformly bounded. All remaining direction norms are 1. The putative bound at derivative order `k+1` therefore fails for every constant, even on any arbitrarily small *fixed low-norm neighborhood* of the reference point. A different constant for each `k` does not help: fix `k>L`, then send `N→∞`.

This phenomenon persists with smooth time cutoffs, a periodic lift, a reference velocity independent of angle, and flows arbitrarily close to the identity. It is caused by composing the varied vector field with the varied flow, not by roughness or endpoint singularities.

## Relation to this specific nonlinear flow

The generic counterexample does not automatically realize every circle vector field by `minusCharacteristicSpeed (originalCoefficients D S C z)`. A potential realization route is available, but has not been fully formalized in this audit:

1. At `q=0`, the actual flow is translation by the radial travel angle. A variation in one control `κ_m` changes the total travel with derivative 1 by the last clause of `controlGeometryConditions`.
2. Each control has compact support strictly inside its negative component. After its support, a control variation changes the accumulated incoming angle while leaving the local reference profile unchanged.
3. A height variation supported in a later compact subinterval supplies high angular Fourier modes in the mixed `q`/height derivative of the characteristic speed. Surjectivity of the physical-space decoder includes such compactly supported even π-periodic smooth heights.
4. Differentiating repeatedly in the earlier control parameter differentiates those transported high-frequency modes. The terms of highest angular degree have precisely the behavior in the two-stage example. A rigorous contradiction for the exact geometry would need an explicit formula for the mixed speed derivative and a noncancellation argument respecting the even-height restriction.

Until that final realization is written, the claim justified here is: **the frozen uniform-in-k flow clause is stronger than its cited manuscript theorem and is false for the standard circle-flow mechanism being invoked.** It should not be reported as an already machine-checked contradiction of `N01Statement`.

## Implemented contract repair

The current `OrdinaryFlowFamilyTameBounds` keeps one common `base`, one positive neighborhood radius `ε`, and the fixed spatial loss `loss : ℕ` used by the remaining nonlinear interface. Its flow conjunct allows an additional parameter loss depending on `k`:

```lean
(∀ k : ℕ, ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ...
  ... oneHighVariationWeight ... base (s + loss + parameterLoss) ...)
```

Here `parameterLoss` is quantified before `s`, the component, the point, the state, and all directions. It therefore cannot hide dependence on any of those variables. An equivalent packaged form is `∃ parameterLoss : ℕ → ℕ, ... high (s + loss + parameterLoss k)`. If one needs a designated zeroth-order spatial loss, impose `parameterLoss 0 = 0` and prove the zeroth-order estimate separately before packaging. Do not replace the common neighborhood by an order-dependent neighborhood. Do not claim `parameterLoss k=k` without proving that rate.

The coefficient clause concerns a finite-order differential expression with pointwise smooth functions and may admit a uniform loss in `k`. There is no need to weaken it merely because the flow clause requires a repair. Allowing order-dependent loss there too would match the manuscript but should be a deliberate, documented choice.

The outer type `N01Statement` remains `∃ ... base loss ε, ... N01Properties ...`. This preserves the cumulative nonlinear type constructors, while the mathematical content of the flow bound changes to the manuscript's quantifier order. `Blueprint/Assembly.lean` explicitly documents that correction. The separate primitive-geometry repair changes the predecessor contract, as recorded in `docs/N01c-geometry-audit.md`; it must not be confused with proving the original unchanged implication.

## Downstream uses checked at the original audit

The initial code search at revision `3a7853f30c9b6253375cc96d22cede2c34b59358` found `ordinaryFlowFamily` and `coefficientFamily` only in their definitions and in `N01Properties`. At that revision, other consumers were endpoint-closure and point-solution modules (`StateControlEndpointClosure`, `StateControlCofiniteClosure`, `MaterialHeightRegularity`, `PointSolutionCore`, `WeakBranchCore`, `ControlCellEndpointBounds`), the cumulative statement files, and the blueprint generator. Their visible uses concerned earlier geometric/control conjuncts or passed the whole proposition through. This is a historical inventory: the current N01c implementation now uses both families throughout its analytic proofs and restriction/assembly modules. The complete current tree and the four actual N01c declarations must pass the build and strict transitive axiom gate.

## Secondary issue: localization of witnesses

`N01PartA` constrains `C.cell m` only through bounded difference of `D.cellIndex`; it does not assert `Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)`. `RadialReturnMargins` provides some containing cell for each negative component, but does not identify it with the chosen `C.cell m`. Thus a proof that preserves *every arbitrary witness* of `N01bStatement` would need extra localization reasoning or data. This does not show the original existential-to-existential N01c implication false; the output may rechoose geometry. Earlier endpoint-closure modules used an explicit `hloc` parameter, and the completed N12 proof uses a different cofinite argument, so the absence is already recognized elsewhere. Do not silently strengthen N01c to a universal same-witness theorem based only on the existing input.
