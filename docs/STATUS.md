# Status

Last updated: 2026-11-11.

## Completed line: R08

`line/R08` proves the unchanged theorem
`R08 (hR03 : R03Statement) (hR07 : R07Statement) : R08Statement`.
It constructs the actual smooth global profile and nonzero second-mode field,
keeps the complete selected natural tails after independent radius and amplitude
scaling, provides every requested logarithmic cone-head length, and preserves
each retained negative component and its radial travel exactly.

The proof includes selected-entry normalization, the actual Morse natural-line
and physical-flatness transport, positive inward cone continuation, a safe
logarithmic-slope cutoff, a positive bridge between pure modes, full-germ central
gluing, and construction of the accumulating cells and trace scaffold.

At proof commit `eba49b574fdcaf641f592f7e12cf721693ba650e`,
[CI passed all 3,938 build jobs](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43003235634).
The blueprint audit lists R08 among the 14 proved nodes and rejects every
nonstandard axiom; R08 has no `sorryAx` dependency. The dedicated
`#print axioms ContinuousFlexibility.Blueprint.R08` is included in the
unfiltered CI status step so its exact standard-axiom list is visible.

The R08 import closure has 265 project modules: its wrapper,
`Blueprint.Statements`, and 263 ordinary proof modules. All 263 ordinary
modules are directly imported by the root. The source audit found no
`sorry`, `admit`, project axiom, `unsafe`, `native_decide`, `sorryAx`,
`ofReduceBool`, `trustCompiler`, `implemented_by`, or `extern` in this
closure, and no missing local import or dependency cycle.
The complete local definition dependency chain of R03Statement, R07Statement,
and R08Statement is unchanged from main.

The natural-line and physical-flatness dependency closure is reused from
`line/R06b` at `eb1f4bd4ed3b73f4112ff2a7c72721c07b0de3aa` and
`line/R06c` at `8a8c4537f12adbc5b0909b8cc81f320d4ab2f3a8`,
with integration fixes checked by CI. These are ordinary proof modules;
the open R06 blueprint nodes are not used. Shared scalar definitions move
from `Statements/Radial.lean` to `Statements/DeepTailOperator.lean`,
retaining their declaration names.

The shared test-support repair is exactly the compact-test clause in
`TailEnergyCore`, `TailWeakDerivative`, and `TailDistributionGraph`:
`Function.support ψ ⊆ Ioo T.entrance endCut` becomes
`tsupport ψ ⊆ Ioo T.entrance endCut`. The ordinary support condition allows
its closure to touch the boundary; the scalar Friedrichs test core requires
compact support inside the open interval. None of these three changes occurs
in the frozen R03/R07/R08 definition dependency chain. The assembly theorem
signatures are unchanged, and `Blueprint/Assembly.lean` documents the repair.

## Completed line: Tame

`line/Tame` proves the unchanged theorem `Tame : H01Statement ∧ H02Statement`.
H01 includes exponential-sequence smoothing and all six frozen calculus
clauses. H02 constructs genuine inverse-family derivatives from the resolvent
identity and proves the required local tame bounds. Ordered-partition
composition and multilinear normalization supply the higher-order estimates,
including order zero and seminorms with nontrivial kernels.

All 15 new proof modules are in the root import. At proof commit
`4e255f2dfff527c143babbdd491762dd8ec8d092`, the default build passed all 3,810 jobs,
the project axiom audit passed, and `#print axioms ContinuousFlexibility.Blueprint.Tame`
reported only `propext`, `Classical.choice`, and `Quot.sound`.
[Verified build](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/42982787838).
No frozen statement or assembly repair was needed.

The [PR integration build](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/42982795292)
also passed with main's completed N12 proof: 3,814 jobs, an axiom audit of
11,066 project declarations (8,324 theorems), and 9 / 42 blueprint statements proved.

## Target

`thm:main` of the manuscript. The statement was first taken from the 62-page version
(`paper/flexible-surface-rewrite/01-introduction.tex`, lines 18–31); the 104-page readable version
(`paper/flexible-surface-readable/`) has the same theorems, constants and labels with more of the
proofs written out, and is the version the task files cite:
a smooth, one-periodic family of isometric embeddings of the standard sphere with two
noncongruent images, fixed inner disk and cap, and constant area, enclosed volume and
total mean curvature.

The manuscript contains no author-flagged unproved step. It treats the oscillator and Morse
spectra and Hamilton's Nash–Moser theorem as standard inputs; none of these is in mathlib.

## Numbers

| | |
|---|---|
| Lean modules compiled / total | 505 / 510 |
| Modules in the root import | 467 |
| Lines of Lean under `src/` | 114,309 |
| Axiom audit (`lake build`, 3,938 jobs) | passed; R08 has only standard axioms |
| Blueprint statements proved / total | 14 / 42 (S01, S02, R01, R02, R03, R04, W01, ScalarCalculus, Tame, R05a, R08, N04Cubic, N04Transmission, N12) |
| Challenge (`FlexibleSphere.exists_closedBending`) | not proved |
| Modules on the module system | 1 (the Challenge) of 514 |

These counts describe the successful R08 proof commit above. The compiled count
is the source import closure of the four successful default targets, restricted
to `src/ContinuousFlexibility/`. It excludes stale artifacts restored from
other branches: the raw cache counter reported 525 / 510 and is not a source
coverage count. Five source files remain outside those default targets, all
unchanged from main and outside R08's dependency closure:
`Analysis.CircleJetEncoding`, `Analysis.CircleJetEvaluation`,
`Analysis.PhysicalJetMollification`, `Analysis.ProjectiveNewtonCommonOrbit`,
and `Analysis.ProjectiveNewtonParameterGrowth`.

## What is proved

- **Central–tail connection (R08).** The unchanged conditional milestone is proved with an actual global second-mode solution, arbitrary exact cone-head length, complete selected-tail retention, and exact negative-component/travel transport.
- **Geometry (paper §2, part of §10).** `mainStatement_of_flatAnnularCore :
  Nonempty FlatAnnularCore → Statements.MainStatement` (`Contracts/SphereClosedBending.lean`).
  The whole remaining problem is `Nonempty FlatAnnularCore`.
- **Endpoint closure (N12).** The unchanged theorem
  `PointBranchStatement → W03Statement → S03Statement → N12Statement` is proved.
  `Analysis/MaterialSampleCofinite.lean`, `Analysis/StateControlCofiniteJets.lean` and
  `Analysis/StateControlCofiniteClosure.lean` prove smooth endpoint extension of the actual
  controlled profile from the existing bounded index shift and weighted control bounds.
  `Analysis/PointSolutionCore.lean` constructs the core from the same normalized nonzero
  solution point. No control-interval placement hypothesis is added. All proof dependencies
  are in the root import; N12 depends only on `propext`, `Classical.choice`, `Quot.sound`.
- **Abstract Nash–Moser, fixed parameter.** `exists_projectiveNewton_fixed_branch`
  (`Analysis/ProjectiveNewtonFixedBranch.lean`).
- **Tame calculus and inverse families.** `Blueprint.Tame : H01Statement ∧ H02Statement`,
  assembled from `Analysis.h01Statement` and `Analysis.h02Statement` with the
  exact frozen hypotheses and conclusions.
- **Lemmas for §5–§9** (21 modules added on 2026-11-11, listed in `docs/archive/2026-11-11-lemmas.md`).

## What is not proved

`Nonempty FlatAnnularCore`, i.e. paper §3–§10: the accumulating radial reference (§4–§6),
the weighted spaces and fixed-type inverse (§7–§8), the nonlinear solution (§9). The passage from a point solution to the endpoint-regular
annular core (§10) is now proved conditionally in N12; existence of that point solution remains open.

## Blueprint v4

`src/ContinuousFlexibility/Blueprint/<Node>.lean` holds one theorem per node; `Blueprint/Statements.lean`
holds the intermediate statements that the earlier statement layer did not have.
`Blueprint/Assembly.lean` composes the nodes to `Nonempty FlatAnnularCore` without `sorry`, and
`FlexibleSphere.exists_closedBending` in the Solution follows; it depends on `sorryAx` exactly
through the open nodes. `scripts/BlueprintStatus.lean` prints proved / total.

The nodes follow the structure of the statements and the lemma structure of the readable manuscript:

- merged small nodes: `ScalarCalculus`, `ScalarWeighted` (S03–S05 by calculus / weighted spaces),
  `Tame` (H01+H02), `Spaces` (W02+W03), `N02N03`, `N09N10`;
- pipelines for large nodes: `R05a` → `R05b`; `R06a` → `R06b` → `R06c`; `R10a` → `R10b`;
  `R11a` → `R11b`; `N01a` → `N01b` → `N01c`; `N04a` → `N04b` → `N04Coordinates`, beside the three
  standalone targets `N04Root`, `N04Cubic`, `N04Transmission`; `N07a` → `N07b`. A later piece takes
  the output of the earlier one as a hypothesis, so all pieces can be worked at the same time;
- weakened: `Solve` produces `PointBranchStatement`, one solution at one nonzero parameter. The
  readable manuscript confirms that the main theorem uses nothing more (§10, proof of the annulus
  theorem); the doubled-weight estimates of §10 are not on the path.

Open nodes (33): ScalarCalculus, ScalarWeighted, Spaces, R05a, R05b, R06a, R06b, R06c, R07, R08,
R09, R10a, R10b, R11a, R11b, R12, N01a, N01b, N01c, N02N03, N04Root, N04Cubic, N04Transmission, N04a,
N04b, N04Coordinates, N05, N06, N07a, N07b, N08, N09N10, Solve.

Tool tasks (5), abstract lemmas that the manuscript isolates and that have no blueprint node; their
Lean statements follow the manuscript and are not frozen: Tool-OneHighFactor (Lemmas 7.2, 7.3),
Tool-AngularCommutator (Lemma 8.4), Tool-SobolevExtension (extension operator, three-lines lemma),
Tool-R10a-Inner (Lemma 6.3), Tool-R10a-Outer (Lemmas 6.4, 6.5).

One task file each in `docs/tasks/` (40 in total).

Whether each node can be derived from its hypotheses is tested by its line. `N12` has
passed this test with its original statement; `Solve` remains open. `R10a` has one frozen statement for the inner and the outer
region together, because the matching data structure of the statement layer interleaves them; its
two regions are carried by the tool tasks.

Not yet checked against the readable manuscript: the kernel clause of the radial reference
(`R12`). The 62-page version left "endpoint-flat kernel" undefined; the readable version defines it
as the kernel on the weighted graph domain.

## Size estimate

The readable manuscript has 6,890 lines of TeX in §2–§10 (62-page version: 4,460). With the playbook
ratios rescaled to it (about 100–190 lines of Lean per line of readable TeX): about 900,000 lines in
total, range 600,000–1,300,000. Current size is about 10% of the central estimate.

## Node sizes

From the line ranges of the readable manuscript at 100–190 lines of Lean per line of TeX. One line
carries about 20,000–30,000 lines. These are sizes of the whole node, before subtracting what
already exists in the tree.

- Above 30,000 even at the low ratio: R10a (42–81k; split by the two tool tasks), N01c (47–89k;
  it carries the proof of Proposition 7.8 for the coefficient and flow families).
- Above 30,000 only at the high ratio: ScalarCalculus (30–58k, mostly present), R05a (30–56k),
  R06a (25–48k), R07 (22–42k, partly present), R09 (17–33k), R11a (17–32k), N02N03 (19–35k),
  N04a (33–62k), N04b (31–59k), N04Coordinates (23–43k), N05 (22–42k), N06 (23–44k), N07a (29–54k),
  N08 (17–32k), Solve (16–31k).
- Below 30,000: ScalarWeighted, Tame, Spaces, R05b, R06b, R06c, R08, R10b, R11b, R12, N01a, N01b,
  N04Root, N04Cubic, N04Transmission, N07b, N09N10, N12, and the five tool tasks.

## Pick next

Running since 2026-11-11 (branch `line/<Task>` exists): N12, Solve, Tame, Spaces, ScalarCalculus,
R05a, R06a. The current state is always `git ls-remote --heads origin "line/*"`.

A line that has finished takes the first task below whose branch does not exist:

1. Standalone, mathlib only: N04Cubic, N04Transmission, N04Root.
2. Pipelines whose first piece is running: R05b, R06b, R06c.
3. Tools used by several nodes: Tool-OneHighFactor, Tool-SobolevExtension, Tool-AngularCommutator.
4. Radial chain: R07, R09, R08, R10b, Tool-R10a-Inner, Tool-R10a-Outer, R10a, R11a, R11b, R12.
5. Scalar and geometry of the iteration: ScalarWeighted, N01a, N01b, N01c, N02N03.
6. Coordinates and inverse: N04a, N04b, N04Coordinates, N05, N06, N07a, N07b.
7. Nonlinear: N08, N09N10.

## Next

1. Lines on the 33 open nodes and 5 tool tasks, one branch `line/<Task>` each (`docs/tasks/README.md`).
2. Module-system migration of the existing files on a branch, verified by CI.
3. `formalization.yaml`, `LICENSE`.
