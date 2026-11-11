# N04b: minimal repair of the physical domain interface

## Decision and scope

Add one state-dependent physical-domain field to `CanonicalData`. Derive the
common cut curve from the actual inverse chart at the canonical cut boundary.
Keep the canonical intervals, their common negative radius, the actual
operator formulas, the transmission equation, the normalization, and the
quantitative conclusions.

This branch implements the statement repair described here, together with
the corresponding Assembly and N04a affine-atlas migration. It adds no
normal-form hypothesis to an earlier node and does not claim that the
repaired N04b coordinate construction has been proved. The mathematical reason for the
repair is documented in [N04b-fixed-cut-audit.md](N04b-fixed-cut-audit.md).

The inventory below was checked against local `line/N04b` through
`76ba527069a4c42b0355ed8be7c1344179d788a5`, with main
`63a4cb2293c1e618dc4aebf5022a9a4cdf30b04a` merged, and against
`origin/line/N04a` at `7870c3bc91ae2f075d829fafee2e55e7000e5c5c` and
`origin/line/N04Coordinates` at `7a710c39ca424751134f091be4a2c6f43a379b69`.
The shared implementation uses one `CanonicalGeometry` structure and one
`CanonicalCutOperatorProperties` predicate, reexported by Part A/B, so the
statement layer and Assembly cannot retain different geometry copies. The
code blocks below specify their clauses; CI validation is reported in the
pull request rather than inferred from this design document.

## 1. Why the interface should allow a curve

Let the genuine travel chart be `(σ,φ)`, with characteristic invariants
`U=φ−σ`, `V=φ+σ`, characteristic drift `d`, and positive speed `v`.
The characteristic equations give

\[
 \sigma_r=v\varphi_\theta-d\sigma_\theta,\qquad
 \varphi_r=v\sigma_\theta-d\varphi_\theta,
\]
\[
 J=v\bigl(\varphi_\theta^2-\sigma_\theta^2\bigr)>0,
 \qquad \varphi_\theta>|\sigma_\theta|.
\]

They make `σ` strictly increasing in radius **with `φ` held fixed**. They
do not make `σ_r` positive with the physical angle `θ` held fixed. For
example, the local derivative matrix

\[
 D(\sigma,\varphi)=
 \begin{pmatrix}-1&1\\-3&2\end{pmatrix}
\]

has `J=1`, `U_θ=1`, `V_θ=3`, and satisfies the displayed identities with
`v=1/3`, `d=5/3`, although `σ_r<0`. This is a counterexample to that local
implication, not a claim to have constructed a complete nonlinear witness
with these jets.

For the inverse travel chart `X`, the middle curve is

\[
 \Gamma_z(\varphi)=X_z(T/2,\varphi),\qquad
 \frac{d}{d\varphi}\Gamma_z^2=\frac{\sigma_r}{J}\circ\Gamma_z.
\]

Writing the cut as `r=c_z(θ)` therefore requires an additional physical-angle
transversality theorem, such as `σ_r>0` on this level. Smallness near the
radial reference can establish such a result on one component; a common
neighborhood for every component requires the appropriate uniform weighted
estimate. Neither conclusion follows merely from the displayed travel-chart
identities.

The recommended repair uses general actual domains and the genuine cut
curve. A proven radial-graph representation can later simplify a constructor
without changing this interface. Merely changing `physicalLeft/right` to
state-dependent real numbers would still permit only circular cuts.

## 2. Data and definitions: one new field

Retain every existing `CanonicalData` field and add

```lean
physicalDomain : (AnnularState S × ℝ) → ℕ → Set PolarPoint
```

Give the existing `physicalLeft` and `physicalRight` an explicit reference
meaning: they are the radial endpoints of the reference physical pieces.
For positive pieces they also remain the current endpoints. For perturbed
negative pieces they must never be used as the definition of the current
domain.

The affected definitions become

```lean
def referencePhysicalPieceOpen (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) : Set PolarPoint :=
  Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ univ

def physicalPieceOpen (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Set PolarPoint :=
  K.physicalDomain z m

def physicalPieceClosed (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : Set PolarPoint :=
  closure (physicalPieceOpen S K z m)

def canonicalClosed (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : Set PolarPoint :=
  Icc (K.left m) (K.right m) ×ˢ univ

def canonicalCutPoint (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) : PolarPoint :=
  K.inverseChart z (K.cutPair m).1 (K.cutRadius m, θ)
```

`canonicalOpen` is unchanged. The cut is a derived object, so there is no
independent curve field whose values could be unrelated to the charts. The
new closed-domain definition uses the actual topological closure, not an
unconstrained set supplied by the constructor.

The definitions of `canonicalHeight`, `canonicalSource`, and
`canonicalOperator` stay exactly as they are. In particular the latter still
uses `divergenceOperator (L.coefficients z)`, the actual composed height,
and the actual Jacobian. The domain repair does not introduce a freely
assigned physical operator.

## 3. Part A: reference geometry, current geometry, and actual boundary germs

Write `z₀=(C.referenceState,0)` and `Ω_z,m=physicalPieceOpen S K z m`.
The following are the exact geometric requirements to retain or add.

### Reference and current domains

Retain the existing strict reference endpoint inequalities, canonical
endpoint inequalities, annular inclusion of the reference intervals, and
their positive/negative reference signs. They concern the reference pieces
named by the existing endpoint fields. Require

```lean
∀ m, physicalPieceOpen S K (C.referenceState, 0) m =
  referencePhysicalPieceOpen S K m
```

For every `z∈stateNeighborhood S C base ε` in the sector and every piece,
require the following predicate. Here `Ω` abbreviates its actual domain;
the displayed types are all fixed by the existing data.

```lean
IsOpen Ω ∧ Ω.Nonempty ∧ Ω ⊆ annularOpen D ∧
(∀ p : PolarPoint, p + (0, Real.pi) ∈ Ω ↔ p ∈ Ω) ∧
(∀ p : PolarPoint, (p.1, -p.2) ∈ Ω ↔ p ∈ Ω) ∧
(K.positive m = true → Ω = referencePhysicalPieceOpen S K m) ∧
(∀ p ∈ Ω, K.positive m = true → 0 < deriv D.w p.1) ∧
(∀ p ∈ Ω, K.positive m = false → deriv D.w p.1 < 0)
```

Nonemptiness also follows from the canonical interval and inverse-map
clauses, but recording it here makes the geometry interface explicit.
Positive physical pieces stay fixed, as in the manuscript. Only the
artificial boundaries between the two negative halves need move.

Replace the reference-only radial partition clause by the statewise planar
partition

```lean
∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
  ∃ E : Set PolarPoint, volume E = 0 ∧
    ∀ p ∈ annularOpen D \ E, ∃! m, p ∈ physicalPieceOpen S K z m
```

This retains uniqueness almost everywhere in the physical annulus. It
does not impose a single radial exceptional set that would contain every
moving cut. At `z₀`, the reference-domain equality and Fubini recover the
old radial almost-everywhere partition. If preserving the existing radial
partition proof as an additional reference clause makes migration easier,
it may be retained; it must not replace the statewise planar clause.

### Normalization

Keep `IsOpen K.normalizationRegion` and
`support (referenceColumn D) ⊆ K.normalizationRegion`. Add equality of the
actual and reference domains in this region, alongside the original chart
and height equalities:

```lean
∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
  physicalPieceOpen S K z m ∩ (K.normalizationRegion ×ˢ univ) =
    physicalPieceOpen S K (C.referenceState, 0) m ∩
      (K.normalizationRegion ×ˢ univ) ∧
  ∀ p ∈ physicalPieceOpen S K z m, p.1 ∈ K.normalizationRegion →
    K.chart z m p = K.chart (C.referenceState, 0) m p ∧
    K.height z m p = K.height (C.referenceState, 0) m p
```

Domain equality prevents the old normalization from becoming vacuous by
moving a piece away from the normalization region. The intended constructor
keeps the positive geometry fixed there and chooses its extension cutoffs
away from the fixed normalization interval. It must prove that choice from
the actual reference data; the repair does not assume that the support of
the normalization column is irrelevant.

### Open charts and symmetries

Retain every old chart and inverse-chart condition, replacing every
`physicalPieceOpen S K m` by `physicalPieceOpen S K z m`:

- mutual `MapsTo` statements and both actual inverse identities;
- smoothness of forward chart, inverse chart, and height on their open
  domains;
- positive height and nonzero actual Jacobian;
- forward-chart π equivariance, height periodicity, both reflection
  identities, and the reflected Jacobian identity;
- inverse reflection on the canonical open strip.

Openness of the physical domain now comes from the new domain predicate.
Proofs must no longer discharge it by `isOpen_Ioo.prod isOpen_univ` unless
they have first specialized to a fixed positive/reference piece.

### Closed charts and the stored inverse

The old closed condition controls only the forward chart and height. Since
the transmission expression differentiates `canonicalHeight` at `ξ=R`, the
stored inverse must represent the actual smooth boundary germ as well.
Otherwise boundary values or off-domain values could enter the totalized
derivative without describing the physical chart.

A precise reusable predicate is

```lean
def CanonicalBoundaryInverseGerm
    (F G : PolarPoint → PolarPoint) (p : PolarPoint) : Prop :=
  ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
    (e : PolarPoint → PolarPoint) = F ∧ p ∈ e.source ∧
    ContDiffAt ℝ ∞ e.symm (F p) ∧
    G =ᶠ[𝓝 (F p)] e.symm
```

For each state and piece let `F=K.chart z m`, `G=K.inverseChart z m`,
`h=K.height z m`, `Ω̄=physicalPieceClosed S K z m`, and
`Π̄=canonicalClosed S K m`. Replace the old `Icc physicalLeft physicalRight`
condition by

```lean
MapsTo F Ω̄ Π̄ ∧ MapsTo G Π̄ Ω̄ ∧
(∀ p ∈ Ω̄, G (F p) = p) ∧
(∀ q ∈ Π̄, F (G q) = q) ∧
(∀ p ∈ Ω̄,
  ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧
  planeJacobian F p ≠ 0 ∧ 0 < h p) ∧
(∀ p ∈ frontier Ω, CanonicalBoundaryInverseGerm F G p)
```

The inverse function theorem supplies the local `e` from forward smoothness
and the Jacobian. The constructor must additionally choose its stored
inverse to agree with those genuine local inverses on a full neighborhood.
This is an actual geometric extension requirement, not the transmission
equation or the normal form in disguise. It implies smoothness of the
stored inverse at canonical boundary points and fixes all derivatives
used by `canonicalHeight` there.

The weaker alternative “closed inverse identities plus `ContDiffAt G`” also
fixes boundary jets by continuity from the interior, but the stated germ
predicate is the recommended contract: it directly matches the existing
cut-pullback helpers, and avoids a second reconstruction of the genuine
inverse germ at each use. Its proof cannot be replaced by assigning
`Function.invFunOn` arbitrary values outside the open strip.

## 4. Part B: the same canonical target on the actual two halves

Keep the current static cut-pair conjunct as a **reference** cut-pair
predicate. Thus both indices remain negative; reference left/right endpoints
are `C.left m` and `C.right m`; their reference interior endpoints agree;
`cutRadius m>0`; and both canonical intervals are `(0,cutRadius m)`.
Those endpoint identities no longer define the perturbed domains.

Add the following current-state predicate for each component. Its signature
needs no reference `D`, because the actual component endpoints are in `C`:

```lean
def CanonicalCurrentCutPair
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) : Prop :=
  let iL := (K.cutPair m).1
  let iR := (K.cutPair m).2
  let R := K.cutRadius m
  let ΩL := physicalPieceOpen S K z iL
  let ΩR := physicalPieceOpen S K z iR
  let Γ := canonicalCutPoint S K z m
  let N := Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)
  (∀ θ, K.inverseChart z iR (R, θ) = Γ θ) ∧
  Set.range Γ ⊆ N ∧
  Disjoint ΩL ΩR ∧
  ΩL ∪ ΩR = N \ Set.range Γ ∧
  K.inverseChart z iL '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
    ({C.left m} ×ˢ (univ : Set ℝ)) ∧
  K.inverseChart z iR '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
    ({C.right m} ×ˢ (univ : Set ℝ))
```

Quantify it over the same `U` and sector as all other current-state clauses.
It can be bundled with the static predicate as the first conjunct of Part B,
so the remaining four outer conjuncts retain their roles:

1. actual cut-pair geometry;
2. the existing transmission equation for every globally smooth physical
   `u`, with precisely `−1/(2*cutRadius m)`;
3. the existing identity for the actual canonical operator;
4. the existing negative canonical coefficients `1,0,−ξ`;
5. the existing positive cubic divided-difference identities.

None of items 2–5 becomes an upstream hypothesis or a freely chosen
structure certificate. In particular the two canonical boundary values
of a physical unknown refer to the same point `Γ θ`, and the full boundary
germ contract makes their radial derivatives genuine pullback derivatives.

The static target can continue to require only a positive fixed radius.
The actual travel construction chooses
`R_m=(3*C.travel m/4)^(2/3)`. Adding that formula as a new assumption of
N04a is unnecessary and would obstruct reuse of its unit affine atlas.

### Consequences that need proofs, not additional free fields

The proposed conditions imply:

- `chart z iL (Γ θ)=chart z iR (Γ θ)=(R,θ)`;
- `Γ` is smooth, injective, π equivariant, reflection symmetric, and has
  nonzero derivative; these follow from the actual inverse germs and the
  nonzero chart Jacobian;
- the closed left domain is its open domain together with the left root
  circle and `range Γ`, and similarly on the right;
- its frontier is exactly that root circle union the cut curve;
- `range Γ` has two-dimensional volume zero, by a countable compact cover
  and the null-image property for a smooth curve;
- every negative piece index belongs to a named cut pair. An additional
  nonempty negative open piece would intersect one of the named halves
  outside the null cut curves, contradicting almost-everywhere uniqueness.

For the last item use N01's coverage and disjointness of the negative
components. Open overlaps cannot be confined to a set of planar volume
zero. A constructor using the existing typed-piece equivalence can instead
prove this index coverage directly. No new arbitrary assignment of an
unpaired negative domain is being permitted.

The exact root image equalities prevent swapping a real turning boundary
with the artificial cut. They identify the whole physical root circles,
not just selected points. A construction should additionally record its
expected angular formulas `(0,h_L θ)` and `(0,h_R θ)`; those useful formulas
are proved from the travel chart rather than required as extra data fields.

## 5. How the genuine travel construction supplies this geometry

Construct the corrected characteristic footpoint maps from the actual N03
operator and form its genuine travel diffeomorphism

\[
 \Psi_{z,m}=(\sigma_{z,m},\varphi_{z,m}):
 (a_m,b_m)\times\mathbb R\longrightarrow(0,T_m)\times\mathbb R.
\]

Prove its inverse `X`, its periodic/reflection identities, its root traces,
and the root regularity estimates. Then define

\[
 \Omega_{z,m,L}=\Psi_{z,m}^{-1}((0,T_m/2)\times\mathbb R),\qquad
 \Omega_{z,m,R}=\Psi_{z,m}^{-1}((T_m/2,T_m)\times\mathbb R).
\]

These formulas refer to preimages inside the actual physical component;
they are not unrestricted preimages of arbitrary totalized values of `Ψ`
outside that component. Their common cut is `X(T_m/2,θ)`.

The open diffeomorphism proves openness, nonemptiness, disjointness, exact
component coverage away from the cut, and the actual sign conditions.
The root-regularized maps

\[
 \xi_L=(3\sigma/2)^{2/3},\qquad
 \xi_R=(3(T-\sigma)/2)^{2/3}
\]

give the fixed canonical intervals. At the cut their inverse germs are the
two actual compositions of `X` with the signed root-travel maps. These are
the hypotheses proved for the concrete constructor before applying
`n04b_canonicalHeight_root_cut`; the repair does not assume those formulas
without constructing `X` and the gauge. At the real roots, the smooth
regularized inverse comes from the root regularity argument and the inverse
function theorem, not from treating a fractional-power expression outside
its valid half-line as smooth.

At the reference state the two domains are radial. Their common radius is
the unique solution of

\[
 \int_{a_m}^{c_m}v_{0,m}=T_m/2.
\]

This reference optical midpoint replaces the arithmetic midpoint used in
the temporary N04a affine construction when constructing the final N04b
atlas. N04b is existential and may rechoose that atlas; the previous affine
choice need not already be the final normal-form atlas.

For the actual statewise partition take the union of the fixed critical
radial lines, positive subdivision lines, and the countably many current
cut curves. Every such set has planar volume zero. The typed negative and
positive component enumeration then proves existence and uniqueness off
that exceptional set. No physical-angle graph theorem is needed.

This is the construction route for the domain predicates only. The
principal-density calculation, the root height factor, the transmission
calculation, the positive matching jets, and all uniform bounds remain
independent conclusions to prove on those domains.

## 6. Source pairing survives without rectangular physical pieces

The repaired source pairing is exactly

```lean
(∫ p in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
  u p * f p) =
  ∫ p in canonicalOpen S K m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
    canonicalHeight S K z m u p * canonicalSource S K z m f p
```

Its existing proof in `CanonicalSourceConversion` uses a physical vertical
segment at fixed radius through all angles. That segment may leave the new
domain, so the old `chart_mapsTo_openAngularStrip` application cannot simply
receive an extra state argument.

Use the inverse instead. Its domain is still the entire fixed canonical
strip. For fixed canonical radius, continuity, reflection, injectivity, and
π equivariance of `G` give

\[
 0<(G(\xi,\theta))_2<\pi
       \quad\Longleftrightarrow\quad 0<\theta<\pi.
\]

For example the zero-axis fiber is unique by reflection and injectivity;
the π-axis fiber follows by translation. The intermediate value theorem on
the canonical angular segment proves the forward interval inclusion.
Translation by integer periods and reflection prove the converse. Combining
this fact with both inverse identities proves

\[
 F\bigl(\Omega_{z,m}\cap\{0<\theta<\pi\}\bigr)
    =\Pi_m\cap\{0<\theta<\pi\}.
\]

Here domain translation/reflection invariance is used to obtain the actual
inverse symmetry identities. This proof makes no assertion that the cut
is a graph in physical angle.

The `Ioc`/`Ioo` difference remains contained in the fixed planar line
`θ=π`, hence is null after intersecting **any** measurable physical domain.
Replace the specialized `polarStrip_Ioc_ae_eq_Ioo` application by this
general null-line intersection lemma. Openness supplies measurability;
the existing actual-Jacobian change-of-variables theorem then applies.
The sign and the height/Jacobian pairing factors are unchanged.

## 7. Transmission and curved physical gluing

The canonical cut transmission identity retains its exact statement. Its
proof now evaluates both canonical unknowns along the same actual middle
curve, using the genuine signed-travel inverse germs and the common gauge.
The existing `N04bCanonicalCut`, `N04bRootCutHeight`, and cut-pullback scalar
calculus already have this form; they do not require a fixed radial cut.

There is a separate migration point for higher physical regularity.
`PhysicalTransmissionTarget` in `Statements/Nonlinear.lean` is explicitly
about a flat physical interface `r=r₀`. It is an independent valid calculus
target and need not be weakened or removed. But it does not apply directly
to the curved middle cut.

To use it there, first flatten the cut with the actual smooth travel chart
near `σ=T/2`, transport the divergence equation and its common source, and
verify the positive normal principal coefficient in that chart. Apply the
local form of the flat-interface gluing result, then transport equality of
jets and smoothness back to the physical variables. A local formulation or
localization lemma may be needed to match the global-function hypotheses
of the current target. This is a genuine proof obligation, not an extra
upstream assumption that transmission already produces smooth gluing.

The true turning boundaries remain radial circles. Existing root collar,
radial Taylor, and positive-piece cubic-division calculations can therefore
keep their radial boundary variables. Only the artificial middle interface
requires the curved-cut transport.

## 8. Exact migration inventory

### Statement layer and assembly

| Location | Required change |
| --- | --- |
| `Statements/Nonlinear.lean`: `CanonicalData` and physical domain definitions | Add `physicalDomain`; add the reference/open/closed domain and derived cut definitions above. Keep all canonical function and operator definitions. |
| `Blueprint/Statements.lean`: current `N04PartA/B` | Replace physical-domain uses, install the current-domain and boundary-germ predicates, and bundle actual cut geometry with the old reference cut identities. |
| `Blueprint/CanonicalParts.lean` on `line/N04Coordinates` | This branch has extracted the same Part A/B definitions here. Apply the repair to the one authoritative definition after integration, and reexport it; do not leave a second stale copy. |
| `Statements/Nonlinear.lean`: `N04Properties` | Install exactly the same repaired geometry and cut clauses, and the state-dependent physical source integral. Preserve the potential/divided-coefficient bound, its quantifiers over all states, constants, and derivative loss. |
| `N04aStatement`, `N04bStatement`, `N04cStatement` | Keep their cumulative existential data and theorem interfaces. Their named property predicates acquire the repaired meanings; no normal-form or jet-bound hypothesis is added to an earlier stage. |
| `Blueprint/Assembly.lean`: `N04_of_nodes` | Assemble the repaired `N04Properties` on the same witnesses and same neighborhood. Keep `RootCompositionTarget`, `CubicDivisionTarget`, and `PhysicalTransmissionTarget` as the independent additional conclusions. |

To prevent the two geometry copies from drifting, a suitable implementation
is to place common named geometry/cut/operator predicates before
`N04Properties` in `Statements/Nonlinear.lean`, and make the blueprint
`N04PartA/B` wrappers refer to those predicates. This avoids an import cycle:
the nonlinear statement layer must not import the blueprint layer. The
existing predicates can instead remain expanded if their equivalence is
proved and checked in the same change; keeping inconsistent copies is not
an option.

The outer assembly theorem currently only unpacks `N04cStatement` and adds
the three independent targets. Its logical argument can remain the same
when the `N04Properties` payload remains whole. If conjunctions are grouped
into named predicates, rebuild the corresponding equivalence and
constructor/projection lemmas, rather than add a stronger premise to
`N04_of_nodes`. The final call chain remains

```lean
N04_of_nodes (N04Coordinates (N04b (N04a hN03)))
  N04Root N04Cubic N04Transmission
```

### N04a branch

| Module | Migration |
| --- | --- |
| `N04PieceData`, `N04SignedPieces` | Retain the actual typed reference partition and its equivalence with natural indices. Its arithmetic negative midpoints describe a valid preliminary reference atlas. Its countable radial exceptional set supplies the planar partition for a state-constant atlas. |
| `N04CanonicalAtlas` | Set `physicalDomain := fun _ m => Ioo (P.left m) (P.right m) ×ˢ univ`. Add `z` to `n04CanonicalAtlas_physicalPieceOpen`. The affine maps have genuine global inverses, so the new boundary-germ contract follows without a normal-form assumption. |
| `n04CanonicalAtlas_partA` | Prove the new constant-domain normalization and actual-domain clauses; lift the countable radial exceptional set to null planar lines. Existing affine symmetry and nonzero Jacobian arguments are retained. |
| `n04CanonicalAtlas_cutPairs` | Rename or document its conclusion as the static/reference cut geometry. It can also prove current component decomposition and shared inverse cut values for this affine atlas, but still does not assert the transmission or Tricomi clauses. |

For the final negative construction, reuse the typed enumeration and replace
its reference midpoint by the proved optical midpoint. The canonical radius
and height are reconstructed from the actual travel data. Retain or choose
`cell` values consistently with the component material estimates; no
state-dependent canonical measure or canonical index set is needed.

### Current N04b modules

| Module | Migration |
| --- | --- |
| `N04bCanonicalOperator` | Add `z` to physical-domain membership and use the new openness field. Its local inverse/Jacobian operator identity is already stated for actual smooth maps and is unchanged. |
| `N04bCanonicalPhysicalAction` | Same domain/openness change; `N04bLocalIntertwining` already accepts general open physical and canonical sets. |
| `N04bPositiveRegularity` | Obtain annular inclusion and positive sign from the actual domain predicate. Positive-domain equality also permits the old radial specialization. |
| `N04bPositiveDivision` | Replace its copied old `hcut` type by the named repaired cut-geometry predicate. Interior canonical cubic division itself is unchanged. |
| `N04bCanonicalCut`, `N04bRootCanonicalCoefficients` | Their signatures use `CanonicalData` but do not define physical pieces from fixed radii. The scalar calculations remain; the actual constructor must supply their inverse/chart/height germs on the new domains. |
| Record updates such as `n04bCanonicalOperatorData` | `{ K with ... }` preserves `physicalDomain` automatically. Add explicit preservation simp lemmas where needed. |

The new principal-determinant, local operator-germ, carré-du-champ, optical
variation, and rotation scalar helpers do not define the physical domain.
Their mathematics is independent of this interface change.

### N04Coordinates branch

| Module or group | Migration |
| --- | --- |
| `CanonicalStripGeometry` | Keep strip-only elementary lemmas. Generalize the canonical application using the actual inverse on the fixed canonical strip, as in Section 6. Add domain invariance premises where needed. |
| `CanonicalSourceConversion` | Add the state argument to the physical integral; use actual-domain openness and the general null angular-line lemma. The Jacobian conversion core remains. |
| `CanonicalBoundaryImage` | Its private `image_not_mem_open_of_boundary_leftInverse` already allows arbitrary sets. Generalize the public canonical wrapper to `p∈frontier Ω`; use `closure Ω` rather than `closure_Ioo`. |
| `CanonicalEndpointInverse` | The inverse function theorem lemma is unchanged. The canonical wrapper uses `p∈closure Ω`; the repaired germ contract directly supplies agreement with the stored inverse. |
| `CanonicalInteriorInverse` | Keep the scalar/radial-strip lemmas as valid special cases. Replace the canonical application by the actual boundary inverse germ, which gives agreement on a whole local canonical neighborhood and hence on its interior. |
| `CanonicalPrincipalCoefficients` | Add the state argument to physical membership and use domain openness. Its coefficient/density calculation and negative coefficient differentiability remain. |
| `CanonicalCoefficientIdentities`, `CanonicalFieldJetReduction` | These operate on the unchanged canonical intervals. Preserve the actual potential identity, cubic quotient, endpoint jet requirements, and finite derivative losses. Update only accessors to the repackaged Part B. |
| `CanonicalJetNormalization` | Record updates preserve domains and curves. Add `z` to the domain-preservation lemma; retain all-state quantitative normalization without changing charts or physical sets. |
| `CanonicalJetObstruction` | The same-witness counterexample remains a statement about unused divided coefficients. Update its Part A/B projections; it does not concern current physical geometry. |
| `CanonicalNeighborhoodRestriction` | All new current-domain, partition, cut, and germ clauses restrict by the same state-neighborhood inclusion. Keep reference geometry unchanged. |
| `OrdinaryFlowJacobianBounds`, `CanonicalReturnJacobianBounds` | Their mathematical statements concern the genuine N01/N02 flows. Only transport of the now-repaired Part A/B through neighborhood restriction changes. |
| `CanonicalCoordinateCompletion` | Rebuild `n04Properties_iff_parts_and_jetBounds` and its constructors with the new clauses and source-pairing theorem. The missing quantitative estimate must still be supplied independently. |

The later definitions `canonicalMeasure`, canonical Sobolev/L² sequence
spaces, `VolumeModelData`, `CanonicalDomainData`, `HasCanonicalRepresentation`,
and the N05 onward cumulative statements use the same `CanonicalData S`
type and fixed canonical intervals. Their representation formulas already
take `z`. They need a compile audit but do not require state-dependent
canonical Banach spaces. Actual reconstruction/gluing arguments must use
the new physical partition and the curved-cut transport from Section 7.

## 9. Review and verification gates

The repair and its eventual constructive proof have these specific verification gates:

- The common domain field is the only new geometric data field; the cut is
  tied to the actual inverse trace, and all boundary derivatives are tied
  to a genuine local inverse germ.
- Every old current-state use of `physicalLeft/right` is either replaced by
  `physicalPieceOpen S K z m`, or explicitly justified by the positive or
  reference specialization. A repository-wide search must include the two
  active coordinate branches when integrating them.
- The planar partition, normalization-domain equality, true root images,
  and exact negative-component decomposition are proved for the actual
  travel construction. An open domain predicate alone is insufficient.
- Canonical interval lengths and the canonical measure remain fixed.
  The actual operator, transmission coefficient, source/Jacobian pairing,
  and quantitative jet bound retain their original mathematical content.
- N04a's revised geometric endpoint still has its direct affine proof.
  N04b does not receive the desired negative normal form, its chosen travel
  chart, its gauge, or the final coordinate bound as an added hypothesis.
- The source conversion proof treats a general physical domain and does
  not use a nonexistent vertical physical segment. Physical gluing across
  the middle curve is transported through a real local chart.
- `N04Properties`, Part A/B, the completion equivalence, and
  `Blueprint/Assembly.lean` agree in one reviewed change. All affected
  modules and the full generated root import compile without new axioms or
  `sorry` before the repaired task is described as complete.

This repair removes the unsupported fixed physical cut while retaining the
mathematical work of constructing and estimating the genuine canonical
coordinates. It does not supply that work by changing the theorem's premises.
