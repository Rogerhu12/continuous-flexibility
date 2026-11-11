# Continuous Flexibility

Lean formalization of *Smooth isometric bending of a closed sphere*,
Boyang Hu, 10 November 2026, supplied as `flex-rewrite-62pp-tex.zip`.

The project uses **Lean 4.35.0-rc3** and pins mathlib to
`c55e6e786f49471c72fbddbec5415808896aec1e`, the matching mathlib release.
`lake-manifest.json` locks the transitive dependencies.

## Build and audit

```powershell
$env:LEAN_NUM_THREADS = '4'
lake build
```

The default build includes `AxiomAudit`. This checks every declaration owned by
an imported project module, including private helpers, as well as declarations
in the `ContinuousFlexibility` namespace. It rejects any transitive axiom other
than `propext`, `Classical.choice`, and `Quot.sound`. It also rejects project
axiom declarations and fails if it finds no project theorems. Modules in the
last integrated checkpoint are imported by `ContinuousFlexibility.lean`.
Parallel work adds further modules; integration must add and audit them before
including them in a new whole-project completion claim.

## Scope

This is an incremental formalization. The implemented modules prove actual
height-coordinate derivatives, Cartan equations and the connection residual,
the full divergence linearization, smooth removable parameter normalization,
normalized-source conservation, corrected type and Green identities,
local smooth planar development, and conditional global planar inversion.
The radial modules include Liouville and measure transformations, actual
Fourier separation and orthogonality, the radial height baseline, and the
central travel-angle small-divisor estimate. A supplied actual annular core now
produces a unique centered oriented smooth development and a genuine Euclidean
three-dimensional graph embedding, with a jointly smooth periodic isometric
graph family fixing the inner and exterior regions. The same core now also
gives an actual separated marked cap and a jointly smooth family of genuine
smooth embeddings of the standard sphere, all inducing one actual smooth
positive Riemannian metric. Actual radial-disk rigidity and variation of the
graph image are proved. The actual marker, shape eigenlines and finite affine
candidates now prove noncongruence of the same-length regular marked-sphere
family, including reflections. The final common-length assembly is separate.

The central radius is constructed from a real integral. Its complete Hermite
Hilbert basis, actual compact-test differential graph, physical weak-energy
closed form, spectral inverse and true radial-logarithmic weighted inverse are
proved, with the actual maximal compact-test radial graph and distribution
transport. Both endpoint all-order estimates and material jets are proved.
The Morse model has its exact ground-state L2 condition, actual closed associated
operator, genuine compact smooth energy core and energy-class weak equation
identification. Actual flat extension,
projective Fréchet spaces, nonlinear curve chain rules, continuous multilinear
jets, actual jet evaluation and first/second composition derivatives,
fixed-loss linear tame calculus and material coordinates/weights are proved.
The complete geometric implication
`mainStatement_of_flatAnnularCore : Nonempty FlatAnnularCore → Statements.MainStatement`
is verified. It uses one actual marked sphere family, including fixed disks,
image noncongruence, its bounded inside and outward normal, and invariance
of actual Hausdorff area, enclosed volume and total signed mean curvature.
The general Liouville and central radial target propositions also pass.
Positive weighted height membership gives a globally smooth flat extension.
The radial control sum of the same weak branch extends smoothly when its
control intervals lie in the assigned radial cells. Together these results
give an actual `FlatAnnularCore` from the nonzero weak branch and its data.
The accumulating radial reference, physical weighted spaces, control
construction and existence of the nonzero weak branch remain open.
The exact material-data target follows from any accumulating profile.
The Morse differential spectrum and the perturbed continuous Dirichlet
problem on a resistance edge are verified. The radial contracts use the
actual mass and resistance intervals and permit overlapping seam covers.

The latest integrated stable milestone passed `lake --wfail build` on
11 November 2026 with 3690 jobs and zero warnings. It contains 3240 public
explicitly stated theorems and 536 private theorem helpers in 264 Lean files
with 67989 source lines, including the target statement files. The owner-based
axiom audit checked 8966 project declarations, including 6638 theorem declarations (the latter
include generated auxiliaries).
Parallel drafts remain outside this checkpoint; their presence does not make
them verified. Exact source hashes are in
`coordination/checkpoint-2026-11-11-radial-contract-wave.json`, with a frozen
source archive. Current exclusions and their owners are checked separately in
`blueprint/validation.json`.

Source correspondence and outstanding dependencies are recorded in
`docs/FORMALIZATION.md`.

An independent review checked all 514 refined work units against a frozen
source snapshot captured at 02:06:30 Taipei time on 11 November 2026: 65 complete,
87 partial, and 362 unimplemented. These counts describe exact task contracts,
not a percentage of the mathematics. Its 101 passing snapshot modules and
owner-based axiom audit are documented in
[the refinement audit](blueprint/refinement/AUDIT.md). The snapshot's unfinished
Morse module was excluded from complete-task evidence. Later live source and
targeted successful builds require a new audit; the main theorem is unfinished.

The detailed main-theorem blueprint is in [blueprint/README.md](blueprint/README.md),
with exact node statements, a dependency graph, Lean evidence and explicit
completion gates. Its 58-node mapping now covers all 3240 public declarations
in the integrated stable checkpoint. `python scripts/check_blueprint.py`
checks that checkpoint's current source hashes, exact evidence coverage and
the unique registered owners of excluded parallel files. The exclusions are
listed explicitly. `--all-current-sources` restores the strict entire-tree
gate required for final completion. Neither mode proves the mathematical goals.

The separate [statement registry](ContinuousFlexibility/Statements/manifest.json)
contains all 58 compiled target propositions, with manuscript and blueprint
links and a passing owner-based audit. Statement compilation does not add any
existence proof to the stable checkpoint.

Cross-chat work packages and exclusive write scopes are recorded in
`coordination/assignments.json`. The verified source checkpoint is
`coordination/checkpoint-2026-11-11-geometry-analysis-wave.json`. Startup prompts are in
`coordination/startup-prompts.json`. Geometry and radial peer chats are bound;
spaces and nonlinear peer roles remain available, with internal agents already
working on their foundations. Exact current file ownership is in
`coordination/active-workers.json`. Integration has created no chats. The integration chat owns public
contracts, build entry points, dependency pins, the blueprint, and final audit.

## Dependency setup

For a fresh checkout, first run `lake update`. To avoid automatically
downloading the entire mathlib cache, use:

```powershell
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
lake update
lake exe cache get Mathlib.Basic.Real.Basic Mathlib.Analysis.Real.Sqrt Mathlib.Analysis.SpecialFunctions.Pow.Deriv Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Linarith Mathlib.Tactic.Convert
lake build
```

The source manuscript is extracted under `paper/flexible-surface-rewrite/`.
The original ZIP remains unchanged.
