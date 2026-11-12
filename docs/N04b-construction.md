# N04b construction work

## Exact endpoint

The endpoint remains `N04b : N04aStatement → N04bStatement`, with the
shared physical-domain repair described in [N04b-domain-repair.md](N04b-domain-repair.md).
Current physical halves are actual state-dependent domains; canonical
intervals and the cut radius stay fixed. The shared statement, Assembly,
and the already proved N04a affine atlas were migrated together.

The parent now assembles two genuine construction statements,
`N04bFieldRealization` and `N04bCanonicalConstruction`. Both remain open.
The first retains the complete N01--N03 witness, including the independent
bilinear smooth tame source error, and supplies actual raw coefficient
regularity and strict type. The second constructs the atlas and all
Part A/B identities from that field. No conditional helper proof closes
either construction statement.

## Reused coordinate calculus

The first checkpoint reuses these complete modules verbatim from
`line/N04Coordinates`, commit
`fe5009423b9ffc766438b51d75377229b1fbc938` (PR #18):

- `src/ContinuousFlexibility/Scalar/SecondProduct.lean`
- `src/ContinuousFlexibility/Analysis/PrincipalCoefficientPullback.lean`
- `src/ContinuousFlexibility/Analysis/DivergenceConjugation.lean`
- `src/ContinuousFlexibility/Analysis/DivergenceFluxPullback.lean`
- `src/ContinuousFlexibility/Analysis/CoordinateDivergenceIdentity.lean`
- `src/ContinuousFlexibility/Analysis/BoundaryTaylorExtension.lean`
- `src/ContinuousFlexibility/Analysis/BoundaryMixedJets.lean`
- `src/ContinuousFlexibility/Analysis/FiniteRadialJets.lean`
- `src/ContinuousFlexibility/Analysis/PrincipalDensityBoundaryJets.lean`
- `src/ContinuousFlexibility/Analysis/CoordinateOperatorConstruction.lean`
- `src/ContinuousFlexibility/Analysis/CharacteristicPrincipalDensity.lean`
- `src/ContinuousFlexibility/Analysis/ScaledRadialPrincipalDensity.lean`
- `src/ContinuousFlexibility/Analysis/CharacteristicRootDensity.lean`
- `src/ContinuousFlexibility/Analysis/RadialAffineDensity.lean`

The modules contain actual product, flux-pullback, coordinate-divergence and principal-density proofs. In particular, `coordinateOperator_explicit_fields` derives the full transformed operator from the local inverse identity, actual smoothness and nonzero Jacobian. The characteristic-density theorems derive the diagonal wave density and root normalization from actual characteristic equations and differentials. They do not assume N04PartB.

This dependency closure is checked again by this branch's full CI. Copying a module is not evidence that the N04b endpoint is complete.

## Construction obligations

The positive-piece cubic clause is an interior identity; its quotient field can be constructed without a boundary estimate. Endpoint smoothness and all-order quantitative estimates are later obligations.

The main remaining construction is a legitimate choice of the cumulative
data and canonical atlas, including actual negative-piece charts and
genuine cut transmission. The manuscript cuts at `σ = T/2`. The repaired
contract records its physical inverse image rather than requiring a
state-independent physical radial cut. The earlier fixed-cut audit is
a mathematical obstruction under investigation, not a Lean refutation
of the old existential statement.

## New proof interfaces

- `N04bPositiveDivision` constructs the actual interior divided coefficients and proves the exact positive-piece clause, preserving the other canonical data.
- `N04bCanonicalOperator` applies the coordinate calculus to the exact frozen canonical operator, from PartA and actual local physical-coefficient smoothness.
- `N04bCutPullback` proves one signed chain rule and the genuine first-derivative transmission matrix for a shared travel pullback with the reciprocal fourth-root gauge.

These are complete helper proofs. They do not assert the outstanding global atlas existence.

## Actual-flow and closed-chart dependency group

The next coordinate dependency closure comes from `line/N04Coordinates`
commit `bd4ec87205383487cfee7e1962d6a76a2835c083`. It contains the actual
periodic scalar-flow construction, parameterized inverse theorems,
characteristic travel-strip bijection, physical root flow and transport,
root smooth height and chart extensions, and the Seeley extension tools.
`CanonicalStripGeometry` and `CanonicalEndpointInverse` are ported to the
current physical-domain contract. `Blueprint/CanonicalParts` is only an
import compatibility module; it does not restore the old predicates.

The fundamental-strip image proof uses the inverse on the fixed canonical
cylinder. It does not assume that a fixed physical radial segment stays
inside a curved current domain. The endpoint inverse proof uses actual
closed inverse identities and smooth local inverse germs.

`N04bCharacteristicFirstIntegrals` and its Transport/Chart modules construct
the actual first integrals from a forward characteristic flow and its
fiberwise inverse. They prove transport equations, angular positivity,
the endpoint and symmetry identities, the whole travel-strip bijection,
and the actual smooth inverse. Instantiating their forward-flow hypotheses
from the cumulative corrected field remains a construction obligation.

## Strict type from the existing N01 hypotheses

`N04bSqrtCrossing`, `N04bProfileLine`, `N04bNegativeProfile`, and
`N04bNegativeDiscriminant` derive strict type on every original negative
component. The actual optical radicand is affine on the state segment
from the reference. The N01 tower makes the actual first radial jet of
the ordinary flow differentiable along this segment. At zero deformation
that jet is the negative optical square root. A transverse zero of the
radicand would contradict this differentiability.

Consequently the actual profile derivative remains negative on the same
N01 state neighborhood. Halving its radius gives a relative lower bound
by half the reference radicand, uniformly across the components. The
exact determinant identity supplies strict hyperbolicity of the original
type-corrected coefficients. These results add no N03 regularity premise.

The two reused helpers `N01RadialFlow` and `SmoothDirectionsScalarLine`
come from `line/N02N03` commit `b2eee1e4b94012e210e91dee039387e64a88df0a`.
All new and reused modules are subject to this branch's full CI; source
review alone is not a compilation claim.

The twelve additional ordinary-flow, angular-variation and compact-integral
helpers are pinned to `line/N02N03` commit
`b7036f0bed67760f4854e757ea2b6c0961494b6c`.
`N04bCharacteristicFlowClosed` and `N04bCharacteristicFlowInterior`
derive closed joint continuity, positive angular variation, periodicity,
and interior smoothness from the stored trajectories and the raw scalar
field. `N04bActualRootSpeedGerm` derives the inward signed square-root
speed factor directly from actual N01--N03 data, with one endpoint
parameter for both roots.

`N04bNormalizationRegion` constructs an actual open region containing
the reference-column support: the complement of the closure of the
reference negative set. Continuity of the actual column gives the
support inclusion, and every negative current domain misses this region.

`N04bReferenceTravelCut` proves that the actual reference optical travel
has a unique interior half-travel radius. `N04bCurrentPartition` uses the
existing signed index type and proves the current planar null partition
by actual travel halves and fixed positive pieces.

## Verified shared-contract checkpoint and main integration

Commit `429d6e089c3e55f48357e8189e73c34c0e5588b3` passed
[full CI run 43063742843](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43063742843):
5,385 jobs; 28 / 42 top-level statements proved and 14 open. The N04a
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
The cache-based module tally printed 1,565 / 1,417 because its numerator
also contains artifacts from modules absent from this branch; it is not
an exact source inventory.

The next checkpoint includes 38 unchanged modules, 4,635 Lean lines,
from main `770c25c151e08589abe17e73357e865a0df2dcd6`. Their blobs also
match main `b6d014ee72e15c1c7537524f0d1bed3052f8bed0`. This is a bounded
dependency-closed integration step before the full main merge, keeping
the distance from green below the repository's 20,000-line limit.

The first reuse checkpoint `8f742e1` passed [full CI run 43043096297](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43043096297): 5,226 jobs; 1,259 / 1,261 modules compiled; 26 / 42 blueprint statements proved and 16 open.
