# N07b: canonical gauge and fixed-domain review

This is a mathematical review of the remaining analytic obligations. It does
not alter a frozen statement, add an assumption to N07b, or assert a completed
counterexample to the existential implication `N07aStatement → N07Statement`.

## What the manuscript's domain lemma actually says

In `paper/flexible-surface-readable/08-stable-inverse.tex`, the lemma labelled
`two-weights-closed-domain` identifies the fixed domain with the range of the
reference inverse on the base canonical source space. Its inclusion of a
smooth canonical unknown requires all of the following:

1. The common transmission conditions.
2. The natural endpoint behavior and normalization.
3. The reference differential expression applied to the unknown belongs to
   the base source space.

The proof subtracts the reference inverse of that reference source and applies
reference homogeneous uniqueness. Smoothness alone is not its hypothesis.

For a current physical solution eta, the candidate reference physical field is,
piece by piece,

    eta_* = h_* ((eta - aL chiLeft) / h_z) o Psi_z^{-1} o Psi_* + aL chiLeft.

Thus a proof using the prescribed N07a witnesses must justify this field's
transmission, endpoint class, normalization, and reference-source membership.
These are genuine analytic steps before the algebraic inverse identity applies.

The preceding manuscript section, `07-fixed-geometry.tex`, explicitly controls
coordinates, inverse coordinates, Jacobians, height factors, source factors,
and their derivatives. Its geometric weight-conversion lemma compares the
piece's material weights with those of its actual physical cell. Its
transmission-domain discussion also matches neighboring positive and negative
pieces at each root. These facts are stronger than the potential and divided
coefficient estimate alone.

## Exact source energy

The source conversion is

    S_z f = (h_z f / |J_z|) o Psi_z^{-1}.

The genuine change-of-variables formula gives

    integral_canonical (S_z f)^2
      = integral_physical (h_z^2 / |J_z|) f^2.

The new `Analysis/N07bCanonicalSourceEnergy.lean` proves this identity by
specializing `canonicalSource_pairing_of_partA`. The raw formula uses
totalized Bochner integrals; it does not infer integrability. Its L2 norm
corollary explicitly assumes actual MemLp of the transformed source.

Consequently a uniform source lift needs control of the actual density
h_z^2 / |J_z|, together with the analogous angular-jet expressions and a
summation over the prescribed piece weights. The pairing identity by itself
does not supply this control.

## A genuine gauge freedom

On a positive piece, let q_m be a smooth positive function of the canonical
coordinates, fixed independently of the state. Leave the chart unchanged and
replace the height by

    h'_z = (q_m o Psi_z) h_z.

Then the actual unknown, source, and operator transform as

    C'_z u = q_m^{-1} C_z u,
    S'_z f = q_m S_z f,
    P'_z W = q_m P_z(q_m W).

Write the positive-piece canonical expression as
`P_z W = -div(A_z grad W) + V_z W`. Direct expansion yields

    A'_z = q_m^2 A_z,
    V'_z = q_m^2 V_z - q_m div(A_z grad q_m).

In particular, the cubic factorization of A_z - A_* remains a cubic
factorization after multiplication by q_m^2. The source density, however,
changes by q_m(Psi_z x)^2. There is no pointwise algebraic estimate for this
density from V_z and the divided principal differences alone: already for a
constant-coefficient divergence operator, identity chart, and constant height
q = A > 0, the potential and state differences vanish while the source density
is A^2. This example concerns those local clauses, not the entire nonlinear
pipeline.

For the reference positive charts actually constructed in the manuscript,
h_* is radial in canonical coordinates. Set initially

    q_0 = 1 / (h_* o Psi_*^{-1}).

The new reference physical height is exactly 1, and its reference potential is
zero because a divergence operator annihilates the constant function. Multiplying
q_0 by a positive constant a_m on each positive piece preserves this fact.

The actual current potential and divided-coefficient differences carry the
factor H_m^beta in the manuscript's stronger estimates. With
a_m = H_m^{-delta}, where 0 < 2 delta < beta, their transformed bounds still
contain H_m^(beta - 2 delta), which does not grow at the tails. In contrast,
the transformed source contains the additional factor H_m^{-delta}.

If S_m = -log H_m and Q_m = log M_m, with Q_m / S_m tending to zero, the
normalized tail amplitudes exp(-sqrt(S_m Q_m)) decay faster than every fixed
power of M_m^{-1}, but multiplication by H_m^{-delta} makes them grow.
Smooth separated bumps with an even nonconstant cosine angular factor are
the natural candidates for a height source with zero angular mean and this
behavior. Checking every physical derivative, rescaling factor, and weighted
sum is required before this becomes a full counterexample.

## What still needs checking in a full gauge construction

The algebra suggests the following transformed reference and relative inverses:

    G'_* = Q^{-1} G_* Q^{-1},
    R'_z = Q R_z Q^{-1},

where Q acts by q_m on the canonical function component and leaves the
three scalar unknowns unchanged.

The boundedness of Q^{-1} would make the reference estimates easier.
The relative conjugation is not justified by the frozen operator-norm bound
alone: Q may be unbounded. One would need the actual off-diagonal kernel
estimate from the manuscript. Its output H_k^beta factor and exponential
decay in |S_k - S_m| are compatible with sufficiently small positive delta,
but preservation of all frozen N05 and N06 clauses has not been formalized
here. The literal maximum physical graph, the derivative estimate, and
the whole-domain inverse identity must each be checked.

Thus this review establishes an explicit gauge mechanism and identifies
what must be ruled out or controlled. It does not claim that a complete
Through06 plus ScalarInverseProperties witness violating the bridge has
already been constructed.

## Existential scope

N07b's outer statement is existential. Even a bad choice of canonical
coordinates satisfying earlier simplified clauses would not by itself
refute the existence of a different, quantitatively controlled choice.

Conversely, replacing the prescribed K is not a formal one-line step.
The volume model, literal reference graph, relative operator, and their
physical identifications depend on K and would also need to be constructed
or transported. The valid next step is to recover the manuscript's actual
coordinate and weight estimates, or construct a controlled set of witnesses,
not to assume the desired source norm or graph inclusion as a new final-node
premise.

## The witness-selection interface does not retain the construction

The exact `N07aStatement` in `Blueprint/Statements.lean` chooses
`A, T, S, C, R, L, K, Vol, b, Domain, Relative, G` together and retains
`NonlinearPropertiesThrough06` and `ScalarInverseProperties` for these same
witnesses. It contains no further predicate identifying `K` with a particular
coordinate construction. The definitions of `Vol`, `Domain`, and `Relative`
depend on `K`; the scalar inverse `G` depends on the chosen physical spaces and
is asserted to solve the operator belonging to the chosen `L`.

The existing N04 interfaces do not supply a replacement theorem for these
dependent witnesses:

- `N04aStatement`, `N04bStatement`, and `N04cStatement` are existential
  statements. A new witness returned by one of their producers need not share
  the old `A`, `S`, `L`, or `K`.
- `N04_of_nodes` in `Blueprint/Assembly.lean` retains the witnesses of
  `N04cStatement` and adds `RootCompositionTarget`, `CubicDivisionTarget`, and
  `PhysicalTransmissionTarget`. These are independent calculus propositions;
  they do not assert that the stored charts or neighboring pieces satisfy
  their hypotheses. There is no separate `N04dStatement` in this interface.
- The proved N04a construction is a reference Liouville atlas establishing
  Part A. It does not identify its charts with the characteristic coordinates
  required by Part B, or transport an already chosen Banach graph to them.

Consequently one cannot destruct `hN07a`, call N04a again, and combine the new
`K` with the old `Vol`, `Domain`, `Relative`, and `G`. Reconstructing all of
these objects is a mathematical alternative, but it requires the corresponding
construction and identification proofs. Calling an open blueprint node does
not discharge those obligations with the permitted axioms.

This is an interface diagnosis, not a proof that the existential implication
is false. In particular, the local gauge example above is not a completed
counterexample to all of Through06, and a bad witness would not rule out a
different good witness.

## Moving physical cuts and the upstream candidate repair

The actual midpoint of a negative component is the level
`sigma_z = T_m / 2` of the current travel coordinate. The canonical cut radius
is fixed, but its inverse image in physical coordinates can depend on the
state and the angle. A state-independent pair of radial intervals does not
describe these current halves in general.

The inspected `line/N04b` snapshot
`419153a8b28df1142bfd0982f60c9d4c0cd99989` already addresses this distinction:
`CanonicalData.physicalDomain z m` stores the current domain;
`referencePhysicalPieceOpen` retains the radial reference interval;
`CanonicalGeometry` states the current partition and boundary properties;
and `CanonicalCurrentCutPair` identifies the common cut by the actual inverse
charts. It also supplies `CanonicalBoundaryInverseGerm`, which prevents
unconstrained values of a stored inverse from determining spurious boundary
derivatives. This is a relevant candidate definition repair, not yet a proved
canonical construction: `N04bFieldRealization` and
`N04bCanonicalConstruction` in that snapshot are open blueprint statements.

The inspected `line/N04Coordinates` snapshot
`442c7c56f82502094bc920ed0746eb54eddd9613` exposes the independent raw ODE target
`N04FlowJetsTarget`. Its coordinate realization subnode is also open, and its
conclusion is still exactly `N04cStatement`. The internal flow theorem alone
does not retain quantitative bounds for every actual stored chart and height
in the later existential witnesses.

## A primitive geometric contract that would support the missing proof

The following describes a proposed upstream output, to be proved for the
actual atlas. It is not an added assumption in an N07b proof. Set
`z_* = (C.referenceState, 0)`, `Omega_z,m = physicalDomain z m`, and
`E_m = T.E0 (T.sample (K.cell m))`. The contract should concern the following
three groups of actual geometric quantities.

### Actual fields and compatible transition jets

Retain raw spatial regularity and angular symmetry of the corrected physical
coefficients, rather than infer them from regularity of a source error.
`N04bFieldRegularity` on the candidate branch is an existing interface for
this purpose. For the Green identity, C1 coefficients suffice; the actual
construction supplies stronger piecewise smoothness.

On the open annulus, construct maps `tau_z` and positive functions `q_z` with
the following exact identities for every current state, every piece, and
every `p` in its reference physical interior:

    tau_z(p) = inverseChart_z,m(chart_*,m(p)),
    q_z(p) = height_*,m(p) / height_z,m(tau_z(p)).

Require these to have a common C2 representative on the open annulus,
preserving the annulus, periodicity and reflection. Their values on the
normalization region are respectively `p` and `1`. These requirements refer
only to coordinate functions and height factors, not to the transformed
unknown or its graph membership. Equivalently one can retain the actual
adjacent-piece jet identities from which this representative is constructed.
Values on the omitted interfaces must be the matching traces, not arbitrary
defaults inherited from a piecewise function definition.

There is a concrete reason for this finite regularity in the manuscript.
At a negative midpoint, write the two charts as `A_i o F_z`, where
`F_z = (sigma_z, varphi_z)` and the scalar root regularizations `A_i` are
state independent. Both transition maps then equal `F_z^{-1} o F_*`.
Writing the physical height as `delta_z^(-1/2) * xi_i,z^(1/4)`, the root
factors cancel in the ratio and give
`q_z = sqrt((delta_z o tau_z) / delta_*)`. Thus the apparent midpoint seam
does not limit regularity. At an actual root, the positive interpolation
matches coordinate jets through order four and logarithmic height jets
through order three. It supports C4 transition coordinates and C3 height
ratios locally across that root, and hence the C2 conclusion needed here.
It does not justify a global C-infinity claim or regularity at the two
natural endpoints. See `positive-crossing`, `current-geometric-jets`, and
`transmission-domain` in the readable geometry chapter.

### Material position and coefficient bounds

The piece label must be linked to its actual physical location. One useful
primitive form is a uniform comparison, on every current piece, of the ratios
of `H`, `E0`, and `M` at the physical radius and at `T.sample (K.cell m)` by
fixed powers of `E_m`. The corresponding comparison at the reference point
and its image under `tau_z` follows because both belong to the same labelled
piece. This is the geometric weight-conversion assertion in the manuscript,
not a new weighted-space membership premise.

The quantitative jet statement needs its constants in the right order.
After choosing one common smaller neighborhood and a fixed loss `d`, it has
the form

    for every order s, there are C_s > 0 and A_s >= 0,
    for every state z in that neighborhood, every piece m,
    and every point in the corresponding domain,
      each specified actual geometric jet of order at most s
        is bounded by C_s * E_m^A_s
          * (1 + stateGrading (s+d) (z.1-referenceState) + |z.2|).

The specified finite list comprises the chart and inverse-chart components,
Jacobians and the reciprocals actually used, heights and reciprocal heights,
and the source factor `h / |J|`. For angle coordinates use their periodic
displacements or restrict values to one fundamental interval; an absolute
bound on a lifted angle over all real angles would be false. Low-order
comparability is uniform on the chosen neighborhood. Higher products must
use this low-order control and the one-high-factor estimate, not multiply
high-order bounds and silently replace a power of the state norm by a
linear expression. No norm of the source field or graph element appears
in this contract.

These bounds are piecewise bounds. Arbitrarily high normal jets need not
match across a positive transition. The global C2 conclusion above and
piecewise higher angular jets are the relevant distinct requirements.

### Consequences that remain theorems, not contract fields

From the actual change of variables, the coefficient bounds, material weight
comparison, and the a.e. disjoint physical partition, one must prove the
canonical source lift and its tame norm bound. Summing the physical integrals
over the partition avoids assuming a uniform number of pieces per material
index. From the same primitive data, the current smooth physical solution
has a C2 reference representative
`aL chiLeft + q_z * ((eta-aL chiLeft) o tau_z)` with the correct endpoint
decay. The finite-regularity Green formula gives its reference weak equation;
the strict exponent gap gives the natural source and output classes; and
reference uniqueness then gives the actual closed-graph inclusion. These
last conclusions are precisely what must be derived, not stored as fields
of an upstream geometric certificate.

## Effect on the blueprint assembly

There are two distinct ways forward. With all current definitions frozen,
one must either derive the primitive facts for the already chosen witnesses
from their existing properties, or prove an independent controlled
construction and carry its witnesses through N05, N06, and N07a. The existing
existential N04 results alone implement neither route.

If the upstream contract is repaired to retain these primitive facts, the
repair must be explicit. `N04PartA` and `N04Properties` must share the current
domain predicate; the N04b producer must establish actual interface matching;
and the coordinate realization must retain actual material and jet bounds.
`N04_of_nodes` must pass this strengthened data, and N05/N06/N07a must retain
it when they shrink the common neighborhood or rechoose witnesses. A
witness-preserving internal realization lemma is preferable to an unrelated
existential choice at each stage. The calls in `flatAnnularCore_nonempty`
must then be checked against these outputs. Existing projection/forgetful
lemmas should expose the old properties needed elsewhere.

The displayed theorem type `N07b (hN07a : N07aStatement) : N07Statement` can
remain syntactically the same under such a cumulative repair, but changing
the definition of its input changes its mathematical assumptions. That must
be documented as a statement repair and checked together with the assembly;
it must not be reported as a proof from the old frozen hypotheses. In
particular, merely appending the desired source norm bound or fixed-graph
membership to `N07aStatement` would move the task into its premise and is
not the proposed repair.

## Minimal executable certificate for the fixed graph argument

The finite base order changes the required quantifiers. N07b does not need
an all-order linear tame estimate in its new geometric certificate. It is
enough to retain, on one common original neighborhood, polynomial bounds

    for every N, there are r, d in Nat and C > 0, A >= 0,
    for every state z, piece m, and point x in its current physical domain,
    every listed material-coordinate geometric jet of order k <= N is bounded by
        C * E0(x.radial)^A * Q_r(z)^d,
    where Q_r(z) = 1 + stateGrading r (z.state-referenceState) + |z.parameter|.

After N05 has chosen b, N07b uses only N = b+2 and the fixed low transport
order. Raise the final base above the finitely many resulting r and take
the radius at most 1/2. `n07b_stateWeight_le_two` makes each Q_r at most 2.
The old inverse, graph, source model, and all witnesses remain unchanged.
The required displayed bridge bound follows from a uniform bound, since
its extra state factor is at least one. This avoids imposing an unnecessary
linear high-order state bound on the repaired coordinate interface.

### Fields which can be defined entirely in Statements

Put beta = 3/4, zstar = (referenceState,0), and write Psi, G, h, J for
the stored chart, inverse, height, and actual `planeJacobian`. All the
following functions are explicit formulas in D, T, S, C, K and the state;
there is no physical source or unknown argument.

At a current physical point x of piece m define

    Theta(x) = G_star,m(Psi_z,m(x)),
    a(x) = h_star,m(Theta(x)) / h_z,m(x),
    V(x) = D G_z,m(Psi_z,m(x)) (0,1),
    X_e(x) = D (G_z,m o Psi_star,m)(Theta(x)) e,
    Omega(x) = ell(x.radial) * |J_z,m(x)|,
    N(x) = sqrt(Omega(x)) * (H(x.radial)/H(sample(cell m)))^beta.

Here e is either (1,0) or (0,1). The use of `fderiv` of an actual
composition is intentional; an inverse derivative formula remains a
theorem following from the actual local inverse relation. No Analysis
definition or theorem is needed to declare these functions.

A sufficient finite scalar family consists of:

- For each Y in {V, X_radial, X_angular}, the three scalar fields
  Y.radial/ell, Y.angular, and `-D Omega(Y)/(2*Omega)`.
- The three seeds `N*h_z/|J_z|`, `N/h_z`, and `N*a`.
- With `B(x)=h_star(Theta(x))/|J_star(Theta(x))|`, the three multipliers
  `B*w'(Theta.radial)`, `B*w(Theta.radial)`, and
  `B*w'(Theta.radial)/Theta.radial`.

This gives 15 explicit scalar functions. For each such g, the certificate
bounds the actual `iteratedFDeriv` of `fun y => g (T.radius y.1,y.2)` at
`(T.rho x.1,x.2)` by the polynomial estimate above. This composition can be
declared directly in Statements; it does not need an Analysis material-chart
definition. These are finite jets of actual geometric functions, not an
operator estimate.
The normalized seeds include the actual sample weight and Jacobian;
unweighted bounds on charts alone would miss precisely that information.
No absolute bound on a lifted angle is requested.

For the global interface and endpoints, retain a second, finite-order
geometric block: maps tau_z and q_z on the open annulus, independent of any
field, which are C3, map the annulus into itself, obey the actual angular
equivariance/reflection identities, and agree on each reference piece with

    tau_z = G_z,m o Psi_star,m,
    q_z = h_star,m / (h_z,m o tau_z).

Bound the actual jets of q through order two and of tau of orders one and
two by `C_z * M^A_z`. In addition retain the pure weight comparisons
`H(tau x)/H(x) <= C_z E0(x)^A_z` and
`M(tau x)/M(x) <= C_z E0(x)^A_z`. These constants may depend on z,
but are chosen before the physical field. They follow from the manuscript's
same-cell weight comparisons; alternatively retain those stronger sample
comparisons and derive these two inequalities. Material absorption then
gives `H(tau x)^beta M(tau x) <= C_delta H(x)^delta` for every delta < beta.
There is no need to store any decay statement about a transported field.

Finally retain C1 regularity and angular periodicity of the actual physical
coefficients L.a, L.b, L.c on the open annulus. The old N03 reflection
identities already give the relevant parity. The new regularity statement
concerns these coefficient functions, not the error operator on a source.

The global C3 statement and arbitrary finite piecewise jet bounds are
different clauses. The latter do not assert matching of all normal jets
across roots. Likewise this certificate does not repair the moving-cut
issue by itself: its piece identities must use the actual current domains
from the N04b repair, with the reference domains used on the reference side.

### Why these primitive clauses close the remaining reference-source step

Write u = H^beta v in material coordinates. For any of the three actual
directions Y, the normalized three-branch coefficient recursion is

    c -> D c(Y) - D Omega(Y)/(2*Omega) * c,
         (Y.radial/ell) * c,
         Y.angular * c.

The first branch keeps the material derivative of v, while the other two
increase its radial or angular order. Thus every resulting coefficient is
a finite differential polynomial in the 15 listed geometric functions.
The reference PDE at Theta(x) is exactly

    w'(Theta.radial) D_Xradial(a*u)
      + w(Theta.radial) D_Xradial^2(a*u)
      + (w'(Theta.radial)/Theta.radial) D_Xangular^2(a*u).

Multiplying by B and applying D_V j times, for j <= b, gives the actual
reference canonical source jets. The required material jets of v have
order at most b+2. The pure geometric bounds and E0^A <= C*M dominate
their squared canonical densities by a finite sum of actual material jet
energies with one extra M weight. More precisely, the existing
`materialE0_rpow_le_subpowerM` gives `E0^A <= C_(A,e)*M^e` for every e>0.
For the angular source chain, e=1/(b+1) supplies the four primitive jet
hypotheses used by the finite product estimate; the complete path then
costs one M, not one M per factor. Change of variables and the disjoint
current atlas sum these energies. No bound on the number of pieces with a
given cell index is used. Compact left-cutoff and reference-column terms
are handled by the same estimate. The angular weak-jet lemma requires only
smoothness on the canonical open piece, so the C3 interface does not force
an invalid global smoothness assumption on the reference forcing.

This derives Fstar in `V.level beta 0 b` at the same beta, rather than
storing it in the certificate. The exponent gap is used separately: choose
weakExponent < delta2 < delta1 < beta, construct the C2 flat reference
representative, and derive its natural source/output classes and weak
equation by `ReferenceGraphFromDecay`. The height seed supplies the actual
canonical unknown and its required weighted zeroth level. N05's literal
graph equivalence now places the pair (U,Fstar) in B.graph. N06, actual
source separation, and `n07aBaseInverse_eq_of_operator` identify U with the
chosen Banach solution. None of these conclusions is a certificate field.

### Exact declaration and projection impact

At the reviewed local snapshot 7103ab9784dd6cb1ba1870a1b0f35b014ada6fe0,
the smallest cumulative placement is a new predicate, for example
`CanonicalPrimitiveGeometry D T S C L K base epsilon`, declared in
`Statements/Nonlinear.lean` after `CanonicalData` and its basic formulas.
Its explicit fields use only existing material functions, `fderiv`,
`iteratedFDeriv`, chart/height formulas, sets, and state gradings. It must
not import Analysis or mention VolumeModelData, CanonicalDomainData,
ScalarInverseData, membership, or norms of a variable physical field.

Keep `N04Properties` and `N04PartA` unchanged for this separate addition.
Append the new predicate to the result of `Blueprint.N04cStatement`, and
to the final conjunction of `NonlinearPropertiesThrough04`. The actual
coordinate producer is responsible for proving it. This makes the new
data pass through N05, N06, N07a and N07 without another existential choice.

The current direct proof edits are exactly two sites, each with a pattern
and a constructor to update:

1. `Blueprint.Assembly.N04_of_nodes`: unpack the extra N04c proof and pack
   it into Through04.
2. `Analysis.N06Neighborhood.n06_NonlinearPropertiesThrough05_mono`:
   unpack it and restrict its state quantifiers to the smaller neighborhood.

Add a standalone monotonicity lemma for the certificate. The bodies of
`n07b_NonlinearPropertiesThrough06_mono` and the Through07 restriction then
continue to call the Through05 restriction. The internal projections of
`N04PartA`, `N04Properties`, N05 and N06 remain unchanged; appending this
separate certificate therefore avoids renumbering their long projections.
`N04Coordinates` has a strengthened output definition, and the assembly
chain must be rebuilt even though its final calls have the same surface
types. The moving-domain repair is a separate, wider change and must be
coordinated with N04b. This is a proposed explicit upstream statement
repair, not a proof from the previously frozen N07a hypotheses.

## Audit of the separate primitive bounds and moving physical cuts

The 15-field proposal above has now been checked against the actual scales
and formulas in the readable manuscript. For the manuscript's normalized
atlas, the separate bounds are supported; a cancellation of negative powers
of the solution weight H is not needed between the reference multipliers
and the normalized seed. This is a statement about the specific geometric
construction, not a consequence of the old frozen N04 predicates for an
arbitrary choice of their witnesses.

### The profile height is not the solution weight

In `05-flat-end-chain.tex`, lines 36--79 distinguish the profile amplitude
`lambda_n = exp(-n^(5/2)+O(n))` from the solution weight
`H_n = exp(-2*n^3/3)`. Lines 284--302 give explicit bounds for every fixed
ordinary derivative of both w and its reciprocal. Their growth is at most
`C_s exp(n^(5/2)+C_s*n^2)`, hence a finite power of E_n. In particular,
the reciprocal of w is not an uncontrolled negative power of H_n.
At a turning circle w is strictly positive: it is w' that vanishes there.
The natural endpoints, where w vanishes, are limits of these pieces and
are not endpoints of any one closed canonical chart.

On a reference negative half, put `Jstar=abs(xi_r)`. The explicit formulas
in `07-fixed-geometry.tex`, lines 1332--1345 and 1395--1404, give

    hstar = (wstar * Jstar)^(-1/2),
    B = hstar/Jstar = wstar^(-1/2) * Jstar^(-3/2).

Both Jstar and its reciprocal have coefficient bounds up to the root.
Consequently the three proposed reference multipliers separately satisfy
coefficient bounds. For example,

    B*wstar  = wstar^(1/2) * Jstar^(-3/2),
    B*wstar' = wstar^(-1/2) * wstar' * Jstar^(-3/2).

The extra division by the physical radius is harmless because the annulus
has positive inner radius. At the root these formulas contain no division
by wstar', xi, or the distance to the turning circle. The canonical length
xi_c and its reciprocal are powers of the Morse scale A_n, so the same
conclusion holds after unit rescaling (lines 1387--1393).

For positive components, lines 1424--1432 and 1469--1485 explicitly bound
the interpolated height, its reciprocal, the inverse coordinate and both
source factors. The general-state inverse and height estimates are proved
in lines 1654--1687, using low-order comparability with the reference
Jacobian and height. The higher-order dependence can be retained as the
polynomial Q_r bound used in the proposed certificate.

### Every normalized seed and direction has the same coefficient scale

The only discrete solution-weight denominator in the three seeds is inside
`R=(H(x.radial)/H(sample(cell m)))^beta`. The geometric weight-conversion
lemma, lines 1505--1540, bounds this ratio by coefficient powers on the
actual cell and its neighbours. Material derivatives of R equal R times
polynomials in material derivatives of log H. These logarithmic derivatives
are bounded, so differentiation does not produce an independent factor
`H(sample(cell m))^(-beta)` that must be estimated on its own.

Thus each of

    N*h_z/abs(J_z),  N/h_z,  N*a

has coefficient bounds separately: N is `sqrt(ell*abs(J_z))*R`, and a
is a ratio of two actual height factors at the corresponding current and
reference physical points. The cell label must refer to this actual
location; an arbitrary old `K.cell` assignment does not establish the
weight comparison.

The nine direction fields have the same property. The directions are
derivatives of actual chart/inverse-chart compositions. Passing to
material coordinates introduces ell and its reciprocal; the drift term
uses the reciprocal of `Omega=ell*abs(J_z)`. Lines 1505--1540 and
1654--1677 control precisely these quantities and their finite jets.
All reciprocals here are of nonvanishing regularized quantities. The
manuscript explicitly excludes use of the reciprocal Jacobian of the
unregularized travel coordinates `(sigma,phi)`, which vanishes at a root
(lines 1674--1677). Likewise, expanding the regularized height through
`delta/sqrt(xi)` and separately bounding delta's reciprocal at the root
would be invalid. The 15-field formulas themselves do neither.

It is therefore unnecessary to replace these 15 actual fields by the
fully expanded reference-source coefficients just to avoid an H loss.
Their geometric proof still has to be supplied for the chosen atlas;
the present review does not promote those estimates to existing Lean
theorems or to consequences of the old existential interface.

### What has, and has not, a compatible fixed-domain model

The reference construction has a concrete radial midpoint r_c, defined by
`sigma_star(r_c)=T/2`, and therefore has fixed physical half-intervals.
The manuscript's general-state construction instead uses
`sigma_z(r,theta) <= T/2` and `sigma_z(r,theta) >= T/2`
(lines 1030--1034). Its assertion that the domain is fixed concerns the
canonical cylinders and transmission relations (lines 1735--1747), not
fixed radial physical half-intervals for all states.

A simple local geometric family shows the distinction. On one negative
component take a smooth radial bump psi, zero near its two roots but with
`psi(r_c) != 0`, and, for small epsilon, set

    F_epsilon(r,theta) = (r + epsilon*psi(r)*cos(2*theta), theta).

Pull back the reference divergence density by this diffeomorphism, and
set `Psi_epsilon=Psi_star o F_epsilon` and
`h_epsilon=h_star o F_epsilon`. The root germs, boundary return maps and
canonical differential expression remain the reference ones. The physical
middle cut is nevertheless

    r + epsilon*psi(r)*cos(2*theta) = r_c,

which is nonradial when epsilon is nonzero. The deformation is confined to
one compact component, so it creates no new endpoint-scale difficulty.
This illustrates the geometric domain issue; it has not been checked
against the specific nonlinear coefficient formulas in N03 or every N05
and N06 clause and is not an existential counterexample to N07a or N07b.

Reference-only atlases, and restricted diffeomorphism families that fix
all cuts, provide models with static physical halves. There is currently
no verified reason that the manuscript's full actual state family belongs
to this restricted class. Therefore the proposed 15-field certificate
cannot be advertised as realized by the actual family while its piece
identities still use the old static physicalLeft/physicalRight interface.
The current physical domains and the reference physical intervals must be
distinguished as in the N04b geometry repair. This requires checking and
porting the actual atlas, change-of-variables and covering arguments; it
cannot be hidden by appending a new estimate predicate to the old fields.

## The coordinated N07b implementation

The implementation couples the dynamic-domain repair above to the
separate primitive geometric certificate. `N04Properties` retains its four
named groups after the domain migration: geometry, cut/operator identities,
the old quantitative coefficient clause, and actual source pairing. The
new `CanonicalPrimitiveGeometry` is appended to `N04cStatement` and
`NonlinearPropertiesThrough04`, and `Assembly.N04_of_nodes` carries the
same certificate into the cumulative construction. It is not inserted into
the conclusion of N07b as a condition to be discharged later.

For precision, the old quantitative clause was:

```lean
(∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z ∈ U, ∀ m p,
  p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
    |mixedDerivative a b (K.potential z m) p| +
    |mixedDerivative a b (K.dividedDifference z m).a p| +
    |mixedDerivative a b (K.dividedDifference z m).b p| +
    |mixedDerivative a b (K.dividedDifference z m).c p| ≤
      B * T.E0 (T.sample (K.cell m)) ^ B *
        (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|))
```

This clause does not mention the geometric quantities below. The extra
certificate makes the missing producer obligations explicit, on the same
state neighborhood and for the same actual charts and sample labels:

| Fields | Actual quantities retained |
| --- | --- |
| Nine direction fields | For each of the current inverse angular direction and the transported reference radial/angular directions: the radial component divided by ell, the angular component, and the logarithmic derivative of `ell * abs(J)` divided by minus two. |
| Three normalized initial fields | `N * h / abs(J)`, `N / h`, and `N * (href at the corresponding point / h)`, where `N = sqrt(ell * abs(J)) * (H / Hsample)^(3/4)`. |
| Three reference multipliers | `(href / abs(Jref)) * w'`, the same factor times `w`, and the same factor times `w' / r`, evaluated at the corresponding reference point. |
| Global finite transport data | Actual transition maps and height ratios, their C3 matching on the open annulus, first two jet bounds, and material comparisons of H and M along the transition. |
| Physical coefficient data | Smoothness and the angular periodicity needed for the actual full-period physical Green identity. |

The `materialJets` constants and polynomial state orders are chosen before
the state, piece, or point. These uniform estimates give the common source
and bulk-coefficient neighborhoods. The lower-order `transport` constants
are chosen after fixing the state; they remain independent of the physical
field, piece, and point. This suffices for the reference graph construction,
which is made separately at each state. The certificate has no physical
source or unknown, no volume model, no reference graph, no inverse operator,
and no final source norm in its fields. The upstream coordinate producer still
has to prove it. Thus the cumulative N04 output is explicitly stronger;
the surface theorem signature of N07b is unchanged, but this is a repaired
statement layer rather than a proof from the previous frozen definitions.

The implementation derives the actual consequences in this order:

1. The original source is encoded in the prescribed `V.level (3/4) 0 b`
   from its true finite angular expansion, coefficient-square bound and
   atlas energy. Its norm is controlled by source grading `b+1`.
2. The primitive reciprocal-height field gives the actual unknown's
   weighted canonical zeroth level, with the loss already selected by N05.
3. The actual transition constructs a global C2 reference representative
   and preserves the physical row. Both endpoint extensions use the same
   general flat-extension theorem.
4. The reference bulk forcing has smooth closed-piece representatives.
   Its true angular jets are finite sums of material jets of the physical
   height. A common physical majorant, independent of the piece label,
   is integrable with order `b+3`. Summing over the actual current atlas
   constructs its source element at the same exponent `3/4`.
5. The genuine physical cutoff flux and reference column have compact
   radial support and zero source mean. Their actual source encodings add
   to the bulk element in the same volume model. `S.chiLeft` is not assumed
   equal to `D.chiLeft`; their compact difference is handled explicitly.
6. A strict exponent gap below `3/4` gives the natural endpoint class and
   reference graph. Only this natural graph uses the weaker exponent;
   the reference forcing remains in the original source level.
7. N05's exact graph equivalence places the constructed pair in the given
   fixed domain. The repaired full-period N06 relation identifies its
   current source. The existing left-inverse identity then identifies the
   complete graph element, preserving the left constant, border scalar
   and zero compatibility scalar.

The final neighborhood is the intersection of the two finite geometric
estimate neighborhoods. Every original witness is retained. The final
source grading is `b+1`; multiplying its uniform bound by the required
state factor is legitimate because that factor is at least one. The
exact endpoint is `N07b (hN07a : N07aStatement) : N07Statement`. Full CI and
the exact standard-axiom audit are the completion gates; the pull request
records the verified commits and audit output.
