# Formalization ledger

The detailed, source-linked main-theorem dependency blueprint is in
[blueprint/README.md](../blueprint/README.md). Its machine-readable node
registry is `blueprint/manifest.json`; this ledger remains the historical
summary of verified implementation milestones.

## Target

The final theorem must construct a fixed smooth metric on a sphere and a
jointly smooth one-periodic family of embeddings into Euclidean three-space.
Each pullback metric must equal the fixed metric. At least two image sets
must be noncongruent under all Euclidean affine isometries. The inner disk
and complementary cap must remain pointwise fixed, and area, enclosed
volume, and total oriented mean curvature must be constant.

An ambient distance-preserving `Isometry` is not the intended definition
of an isometric immersion. Inequality of parameterized maps is not the
intended definition of noncongruence.

## First milestone source correspondence

| Module | Manuscript source | Coverage |
| --- | --- | --- |
| `Scalar/Definitions.lean` | Section 3, `eq:height-jet-notation`, `eq:cart-curvature-scalar` | Explicit coordinate expressions and a coordinate positive-definiteness predicate |
| `Scalar/Positivity.lean` | Section 3, positivity assertion after `eq:height-jet-notation` | Discriminant criterion, diagonal positivity, determinant, and completion of the square |
| `Scalar/Coframe.lean` | Section 3, displayed coframe after `eq:height-jet-notation` | Equality of the sum of coframe squares with the remainder quadratic form |
| `Scalar/Determinant.lean` | Section 3, `eq:cart-determinant-identity`, `eq:cart-completed-normalized-derivative`, radial specialization | Pointwise coefficient identities and explicit coordinate residual; the curvature interpretation is still pending |
| `Radial/Gauge.lean` | Section 5, `eq:rad-eq-rm13` | Actual first and second derivatives of the logarithmic power gauge, and the transformed radial Jacobi expression |
| `AxiomAudit.lean` | Project validation | Checks project-owned declarations, including private helpers, and their transitive axiom dependencies |

## Verified initial milestone on 10 November 2026

`lake build` completed successfully with 2296 jobs. The default axiom audit
reported:

```text
Axiom audit passed for 112 project declarations (93 theorems)
Build completed successfully (2296 jobs).
```

There are 35 explicitly stated source theorems: 10 in `Positivity`, 1 in
`Coframe`, 14 in `Determinant`, and 10 in `Gauge`. The audit's larger theorem
count includes automatically generated equation and auxiliary theorems.
The final build emitted no warnings. Source scanning found no `sorry`,
`admit`, `native_decide`, `unsafe`, or custom axiom declarations in the
project's proof modules.

The installed compiler and mathlib checkout were also checked directly:

```text
Lean 4.35.0-rc3
mathlib c55e6e786f49471c72fbddbec5415808896aec1e
```

These results cover the modules in the table above. The geometric
interpretation, analytic existence arguments, and final closed-sphere
theorem remain open tasks in this formalization.

## Implemented coordinate and reconstruction stage

The later implementation connects the coordinate algebra to actual functions.
The following results have individually passed Lean, with all source and
derivative conventions visible in their statements:

| Modules | Verified scope |
| --- | --- |
| `Scalar/HeightDerivatives`, `ConnectionVariation`, `CoframeDerivatives`, `Connection`, `Cartan` | Actual height partials, mixed-partial compatibility, coefficient derivatives, Cartan equations, and `dα = r N dr ∧ dθ` |
| `Scalar/HeightVariation`, `LinearizationAlgebra`, `Linearization` | Actual directional derivative along `z+tη`, including the full symmetric divergence formula and actual third-jet cancellation |
| `Scalar/Normalization`, `Radial/RadialHeight` | Exact quadratic numerator factorization, real-parameter smooth removal of `q=0`, actual radial base `D=1` and `N=0`, and normalized value at zero equal to the real radial PDE |
| `Scalar/Conservation`, `NormalizedConservation` | Genuine rectangle FTC/Fubini, periodic connection, boundary-jets compatibility, and normalized-source zero mean for every `q`, including zero |
| `Scalar/TypeCorrection`, `GreenIdentity` | Actual corrected coefficients, determinant sign and zero set controlled by `w'`, exact divergence error, and Green identities with explicit periodic and radial boundary conditions |
| `Radial/Liouville`, `RadiusChange` | Actual differential conjugation and explicit ordinary/spectral integration densities |
| `Radial/CentralSmallDivisor`, `CentralTravelAngle` | Actual central travel-angle integral and the lower bound `1/(8 k)` for every positive integer frequency |
| `Radial/FourierModes`, `FourierOrthogonality` | Actual single/finite-mode separation, even half-turn sector, and normalized angular-integral orthogonality of positive cosine modes |
| `Geometry/RotatedCoframe`, `GaugeConnection`, `Primitive`, `HeightCoframe`, `FlatDevelopment`, `LocalInverse` | Actual closed rotated forms, primitives on convex open sets, smooth local remainder-metric development, and genuine local inverse |
| `Geometry/GlobalInverse` | Properness, closedness, compact fibers for a continuous planar map fixed outside a compact set, and preservation of a region by an identity-outside bijection |
| `Geometry/GlobalCovering` | Proper local homeomorphism of the plane gives a genuine global inverse via covering lifts; smoothness and bijective actual derivatives give an actual smooth inverse |
| `Scalar/FlatCollar`, `Contracts/Annular` | Actual constant/zero germs, analytic core interface, and a proved enlargement preserving the same height/profile and producing genuine open collars |
| `Contracts/CartesianHeight`, `CartesianMetric`, `CartesianMetricRegularity` | Actual branch-cut/center-safe Cartesian height, real tensor pullback, global smooth positive remainder matrix and standard inner/outer regions |
| `Geometry/CartesianCoframe`, `CartesianDevelopment`, `CartesianExterior`, `CartesianMetricCoframe`, `MatrixDevelopment` | Actual Cholesky/Cartan data, full-plane integration, circular exterior normalization, global inverse and disk preservation |
| `Scalar/FormPullback`, `Geometry/CoframeRotationAlgebra`, `CoframeSO2`, `CoframeCurvature`, `PullbackCurvature`, `Contracts/CartesianFlatness` | Actual coordinate/exterior naturality and angle-free SO(2) curvature invariance, yielding Cartesian connection closedness from the supplied core's residual without a new flatness hypothesis |
| `Contracts/PlanarDevelopment`, `IsometricGraph`, `Geometry/GraphEmbedding`, `PlanarOrientation` | Supplied core produces one actual globally normalized development with positive Jacobian and smooth inverse, then a genuine E3 graph embedding and its full intrinsic metric identity |
| `Radial/GaussianLaplace`, `CentralRadius`, `CentralRadiusMetric`, `CentralModel` | Real integral construction, actual radius ODE/positivity/inverse, genuine positive profile and actual second-mode solution |
| `Radial/OscillatorKernel`, `HermitePolynomial`, `OscillatorSpectrum` | Ground-state classification in the stated actual C2/L2 energy domain, all Hermite-Gaussian eigenfunctions, actual energy-domain membership and integral orthonormality |
| `Analysis/FlatExtension`, `Graded` | Actual smooth endpoint extension from all derivative limits, and a complete locally convex metrizable projective Banach limit with monotone grading |

The integrated stage passed the full default build on 11 November 2026:

```text
Axiom audit passed for 1398 project declarations (1147 theorems)
Build completed successfully (3087 jobs).
```

That historical checkpoint contains 678 public explicitly stated theorems and 13 private proof helpers
in 65 project Lean source files, with 10842 total source lines including comments
and blank lines. No `sorry`, `admit`, `native_decide`, `unsafe`,
or project axiom declarations were found in the source scan. The compiler
verified the imported modules and their project-owned axiom dependencies.

## Verified coordinated milestone on 11 November 2026

Sixteen additional modules are now imported by the root entry point:

| Modules | Verified scope |
| --- | --- |
| `EuclideanRigidityCoordinates`, `EuclideanRigidity`, `DevelopmentSymmetry`, `CenteredDevelopment` | Actual coordinate rigidity, normalized uniqueness, oddness, center fixing and centered rotation on the inner closed disk |
| `PlanarRotations`, `GraphRotationFamily`, `GraphFamilyImage` | Genuine jointly smooth period-one graph family, each embedding/immersion with one metric, fixed inner/exterior regions, actual E3 axial isometries and closed-disk image identities, uniform height bounds |
| `SurfaceGeometry`, `GraphSurfaceGeometry` | Actual first/second derivative forms and shape, Weingarten relation, graph K/H formulas and arbitrary affine Euclidean isometry naturality, including reflections with transported normals |
| `MarkerBump`, `MarkedCap` | Actual compact smooth integral bump, real derivatives, genuine graph curvature formula and unique strict peak, distinct center shape eigenvalues; no cap existence theorem |
| `TameLinear`, `MaterialWeights`, `MaterialCoordinate` | Fixed-loss linear tame continuity/closure, actual weight envelopes and vanishing, true left endpoint material coordinate derivatives/inverse/limits |
| `ExponentialMoments`, `HermiteCompleteness` | Entire-MGF moment uniqueness and genuine real whole-line L2 Hermite totality, including actual Lp classes |

```text
Axiom audit passed for 1851 project declarations (1549 theorems)
Build completed successfully (3403 jobs).
```

The command was `LEAN_NUM_THREADS=4; lake --wfail build` (PowerShell environment
syntax is shown in the README). It passed without warnings. This checkpoint
contains 934 public explicitly stated theorems and 16 private theorem helpers
in 81 Lean files, with 14121 lines including comments/blanks. The manuscript
and locked dependency/toolchain versions remain unchanged. Exact source hashes
are in `coordination/checkpoint-2026-11-11-coordination.json`. The preceding
checkpoints remain immutable historical records.

These are local or explicitly conditional results. In particular:

- `ContDiff ℝ ∞` means smooth; the top value of `ℕ∞ω` means analytic.
- `PolarPoint = ℝ × ℝ` has the product max norm. The metric identities use
  explicit coordinate dot products and square sums, not its norm squared.
- A polar connection may have period `2π` on an annulus. No global real
  primitive is assumed there. The supplied-core construction now proves
  actual Cartesian flatness and a globally normalized development.
- `FlatAnnularCore` is an input interface whose nonemptiness is unproved.
  The core-to-graph construction supplies no nonlinear existence theorem.
- The actual development is orientation preserving. Its uniqueness, oddness,
  `P(0)=0`, and centered inner closed-disk rotation are now proved from actual
  derivative metric identities, separately from covering-lift uniqueness.
- For sphere attachment choose the enlarged radius `R>b`, using the actual
  larger-disk image theorem. Source nonradial witnesses are preserved; they
  do not alone prove noncongruence of graph images or of closed spheres.
- Compatibility from boundary jets does not require a constant germ or
  equality of the two endpoint height values.
- Smooth removal of `q=0` here is actual smoothness in the real parameter
  at a fixed spatial point. Weighted-space smooth tame estimates and a
  common neighborhood for all seminorms have not been proved.
- Green identities on the closed annulus require actual coefficient
  extensions at flat endpoints. The convenient `Q ≠ 0` regularity theorem
  applies in the interior and cannot establish that endpoint extension.
- Finite Fourier separation and orthogonality do not establish infinite
  Fourier completeness, the closed radial operator domains, or an inverse.
- Actual Hermite-Gaussian L2 completeness is now proved by signed moments
  and an entire complex MGF. The closed differential operator domain, full
  spectral realization and quantitative resolvent bounds remain open.
- The actual flat-extension theorem still requires all derivative limits;
  these have not been derived from the manuscript's weighted estimates.
- The projective Banach-limit model is not a Nash–Moser theorem. Actual
  weighted-space identification, smoothing and tame iteration remain open.

The source scanner counts public theorems with attributes such as `@[simp]`
as well as plain declarations. Private helpers are included in the module-owner
axiom audit. Blueprint evidence and current declaration counts are generated
from the same source by `scripts/check_blueprint.py`.

## Cross-chat coordination

The authority for work ownership is `coordination/assignments.json`.
`coordination/checkpoint-2026-11-11-coordination.json` records the latest
verified source hashes and build result; preceding checkpoints remain historical.

The integration chat owns public contracts, scalar infrastructure, root
imports, the axiom audit, toolchain/dependency pins, blueprint updates, and
the final theorem. Other chats take exclusive radial, analysis, nonlinear,
or geometry packages. Existing compiled interfaces are the starting point;
changes to a shared interface are registered with integration before use.
Every delivery must include the exact Lean statement, paper correspondence,
files or patch, actual build output, new imports, and remaining obligations.
The blueprint validator checks that each of the 55 required nodes has one
work-package owner. The existing geometry peer chat `01a1c655-f121-77d3-adab-122cc010840b`
is now bound and has delivered four frozen modules. Integration created no chats;
the radial, spaces and nonlinear peer roles remain unbound. Copyable startup prompts are in
`coordination/startup-prompts.json`; reconcile active worker leases before binding
a new peer. Planning roles is not evidence of dispatch.

## Planned proof dependencies

1. **Function-space bridge.** Preserve the proved actual coordinate
   derivatives, Cartan equations, divergence linearization and conservation
   while proving the required uniform weighted-space mapping properties.
2. **Weighted spaces.** Define the height, source, circle, and control spaces;
   identify the actual projective-limit model, prove estimates and smoothing,
   and derive the derivative limits required by the proved flat-extension
   theorem. Preserve the free difference between the two endpoint heights.
3. **Radial reference.** Complete the closed spectra beyond the proved
   central radius, ground kernel and orthonormal eigenfunctions; prove bounds,
   construct the accumulating cells, identify the continuous and discrete
   operator domains, prove the unique endpoint-flat solution lines, select
   one parameter sequence for all frequencies, and assemble the bordered
   two-sided inverse on compatible sources.
4. **Geometric closure, parallel to the analysis.** Use the proved core-to-graph
   construction and its proved centered periodic graph family, construct the
   marked fixed cap and sphere charts, then prove noncongruence and actual
   integral invariants.
5. **Stable inverse.** Fix type-change circles and characteristic returns;
   prove the common closed domain and a bounded relative operator with norm
   below one on one Banach space before lifting regularity.
6. **Nonlinear existence.** Formalize the required tame calculus and either
   Hamilton's quadratic-error implicit theorem or an applicable explicitly
   proved Nash–Moser iteration. Verify the exact identity with two independent
   residual arguments and construct the weak annular solution branch.
7. **Main theorem.** Obtain flat endpoint collars, fix one nonzero construction
   parameter, and apply the proved geometric closure theorem.
8. **Remaining manuscript results.** Prove the doubled endpoint weight,
   quadratic metric-control estimates, and the appendix's finite-angular
   obstruction. Section 10 explicitly states that the weak positive weight
   already suffices for the flat endpoint extensions needed for closure.

## Proof obligations requiring early review

- The continuous deep-tail realization and its domain cannot be inferred
  solely from an invertible discrete matrix.
- Simultaneous parameter selection must prove `exists parameters, forall
  frequencies`, with one fixed geometry.
- The even, half-turn-invariant cosine sector is essential to the claimed
  one-dimensional second-mode kernel.
- Sources use the stated `dr dθ` density; coordinate and spectral changes of
  measure must remain explicit.
- The two endpoint constants may differ. The right constant is normalized;
  the left difference is a separate scalar.
- Neumann inversion requires an actual bounded endomorphism of one common
  Banach space. Derivative-loss estimates alone are insufficient.
- High-order estimates must hold on one fixed low-order neighborhood.
- The Hamilton/Nash–Moser dependencies require proofs, not new axioms.

## Provenance

Original archive SHA256:
`B0DA6BFF608DDD2B30FA097ACB8E648CC4AF68B9833C9C4C4CBA1E0809738721`.

Source text is under `paper/flexible-surface-rewrite/`. The archive and
manuscript have not been edited.
