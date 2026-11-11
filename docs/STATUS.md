# Status

Last updated: 2026-11-11.

## Target

`thm:main` of the 62-page manuscript (`paper/flexible-surface-rewrite/01-introduction.tex`, lines 18–31):
a smooth, one-periodic family of isometric embeddings of the standard sphere with two
noncongruent images, fixed inner disk and cap, and constant area, enclosed volume and
total mean curvature.

The manuscript contains no author-flagged unproved step. It treats the oscillator and Morse
spectra and Hamilton's Nash–Moser theorem as standard inputs; none of these is in mathlib.

## Numbers

| | |
|---|---|
| Lean modules compiled / total | 319 / 327 |
| Modules in the root import | 319 |
| Lines of Lean under `src/` | 87,633 |
| Axiom audit (`lake build`, 3751 jobs) | passed: 10,671 declarations, 8,043 theorems |
| Blueprint statements proved / total | 7 / 37 (S01, S02, R01, R02, R03, R04, W01) |
| Challenge (`FlexibleSphere.exists_closedBending`) | not proved |
| Modules on the module system | 1 (the Challenge) of 329 |

The 8 modules that do not compile are unfinished files of the earlier workflow:
`Analysis.CircleJetEncoding`, `Analysis.CircleJetEvaluation`, `Analysis.PhysicalJetMollification`,
`Analysis.ProjectiveNewtonCommonOrbit`, `Analysis.ProjectiveNewtonParameterGrowth`,
`Radial.MorseChainPartitionTrace`, `Radial.MorseChainRealization`, `Radial.MorseChainSelectedJets`.

## What is proved

- **Geometry (paper §2, part of §10).** `mainStatement_of_flatAnnularCore :
  Nonempty FlatAnnularCore → Statements.MainStatement` (`Contracts/SphereClosedBending.lean`).
  The whole remaining problem is `Nonempty FlatAnnularCore`.
- **Abstract Nash–Moser, fixed parameter.** `exists_projectiveNewton_fixed_branch`
  (`Analysis/ProjectiveNewtonFixedBranch.lean`).
- **Lemmas for §5–§9** (21 modules added on 2026-11-11, listed in `docs/archive/2026-11-11-lemmas.md`).

## What is not proved

`Nonempty FlatAnnularCore`, i.e. paper §3–§10: the accumulating radial reference (§4–§6),
the weighted spaces and fixed-type inverse (§7–§8), the nonlinear solution (§9) and its
endpoint regularity (§10).

## Blueprint v3

`src/ContinuousFlexibility/Blueprint/<Node>.lean` holds one theorem per node; `Blueprint/Statements.lean`
holds the intermediate statements that the earlier statement layer did not have.
`Blueprint/Assembly.lean` composes the nodes to `Nonempty FlatAnnularCore` without `sorry`, and
`FlexibleSphere.exists_closedBending` in the Solution follows; it depends on `sorryAx` exactly
through the open nodes. `scripts/BlueprintStatus.lean` prints proved / total.

v3 regroups the 35 nodes of v2 by the structure of their statements:

- merged: S03–S05 are now `ScalarCalculus` (pointwise calculus) and `ScalarWeighted` (weighted
  spaces); H01+H02 → `Tame`; W02+W03 → `Spaces`; N02+N03 → `N02N03`;
  N09+N10+H03+N11 → `Solve`;
- split: R05 → `R05a` (realization), `R05b` (mass and resistance); R06 → `R06a` (inverse),
  `R06b` (natural line, Green kernel), `R06c` (physical flatness, continuity); R10 → `R10a`
  (inner and outer pieces), `R10b` (matching); R11 → `R11a` (weighted bound), `R11b` (first normal);
  N04 → `N04Root`, `N04Cubic`, `N04Transmission` (three statements that use mathlib only) and
  `N04Coordinates`; N07 → `N07a` (scalar inverse), `N07b` (Banach bridge);
- weakened: `Solve` produces `PointBranchStatement`, one solution at one nonzero parameter,
  instead of a branch that is smooth in the parameter. The main theorem fixes one nonzero
  parameter; the existing bridge to `FlatAnnularCore` uses only the pointwise part.

Open (30): ScalarCalculus, ScalarWeighted, Tame, Spaces, R05a, R05b, R06a, R06b, R06c, R07, R08, R09,
R10a, R10b, R11a, R11b, R12, N01, N02N03, N04Root, N04Cubic, N04Transmission, N04Coordinates,
N05, N06, N07a, N07b, N08, Solve, N12. One task file each in `docs/tasks/`.

The split statements are pipelines: a later piece takes the output of the earlier piece as a
hypothesis and re-asserts it for possibly larger constants, so all pieces can be worked in
parallel. Whether each node can be derived from its hypotheses is tested by its line; N12 (the
last link) and `Solve` are the first real tests of the chain.

Not yet split although large: `R10a` (paper §6 lines 231–522, about 50,000–90,000 lines by the
ratios below). Its line should first separate the inner assembly from the outer transition region.

## Size estimate

Paper §2–§10 is 4,460 lines of TeX. With the playbook ratios (105–320 lines of Lean per line
of TeX; hard analysis at the high end) and the measured 110 for §2: about 900,000 lines in
total, range 600,000–1,300,000. Current size is about 10% of the central estimate.

## Challenge and comparator

- `src/Challenge/FlexibleSphereChallenge.lean` states the theorem with mathlib only (198 lines, a module).
- `src/Solution/FlexibleSphereSolution.lean` copies its definitions and proves
  `FlexibleSphere.exists_closedBending_of_core : Nonempty FlatAnnularCore → Nonempty ClosedBending`
  (standard axioms only). The project's `Statements.ClosedBending` transports to the Challenge
  structure field by field, so no bridging layer is owed at the end.
- `src/Challenge/comparator.json` names `FlexibleSphere.exists_closedBending`; the Solution does not
  contain that theorem yet, so the comparator cannot pass.
- `formalization.yaml` and `LICENSE` are not written.

## Module system

`scripts/to_module.py` converts a file mechanically (`module`, `public import`,
`@[expose] public section`). Pilot on copies of the 23 modules that import only mathlib:
23 of 23 compile as modules. The other 304 files have not been tried; they must be converted
bottom-up, and the full rebuild belongs in CI.

## CI

Repository: https://github.com/Rogerhu12/continuous-flexibility. `.github/workflows/build.yml` runs on
`main`, on `line/**` branches and on pull requests.

First green run: 2026-11-11, commit `b4a8fc1` (run 42967068736). `lake build` of all libraries
including the axiom audit passed (3787 jobs); modules compiled / total 355 / 363 (the 327 earlier
files plus the 36 blueprint files; the 8 that do not compile are the unfinished files listed above);
blueprint 6 / 35. A build from an empty project cache takes about 20 minutes on the GitHub runner;
with the cache restored, about 5 minutes. The compiled build is published as `lake-build.tar.zst`
(62 MB) on the `lake-cache` release.

## Node sizes

Estimated from the manuscript line range of each node at 168–320 lines of Lean per line of TeX.
One line carries about 20,000–30,000 lines.

- Above 30,000 even at the low ratio: R10a (49–93k), N04Coordinates (31–59k).
- Above 30,000 only at the high ratio: R05a (27–52k), R06a (25–47k), R07 (27–51k), R09 (22–42k),
  R11a (24–46k), R12 (25–48k), N01 (30–58k), N02N03 (20–38k), N05 (27–51k), N06 (25–47k),
  N07a (29–54k), N08 (21–40k), Solve (17–33k).
- Below 30,000: ScalarCalculus, ScalarWeighted, Tame, Spaces, R05b, R06b, R06c, R08, R10b, R11b,
  N04Root, N04Cubic, N04Transmission, N07b, N12.

## Next

1. Lines on the 30 open nodes, one branch `line/<Node>` each (`docs/tasks/README.md`).
2. Module-system migration of the existing files on a branch, verified by CI.
3. `formalization.yaml`, `LICENSE`.
