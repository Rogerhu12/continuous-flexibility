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
