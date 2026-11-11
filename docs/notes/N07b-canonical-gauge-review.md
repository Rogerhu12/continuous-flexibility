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
