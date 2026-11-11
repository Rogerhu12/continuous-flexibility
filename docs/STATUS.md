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
| Blueprint statements proved / total | 6 / 35 (S01, S02, R01, R02, R03, R04) |
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

## Blueprint v2

`src/ContinuousFlexibility/Blueprint/<ID>.lean` holds one theorem per node on the path to
`Nonempty FlatAnnularCore`: the statements of its dependencies imply its own statement.
`Blueprint/Assembly.lean` composes the 35 nodes without `sorry`, and
`FlexibleSphere.exists_closedBending` in the Solution follows; it depends on `sorryAx` exactly
through the open nodes. `scripts/BlueprintStatus.lean` prints proved / total.

Open (29): S03, S04, S05, R05–R12, W01–W03, H01–H03, N01–N12. One task file each in `docs/tasks/`.

The node statements are those of the earlier statement layer, so the assembly holds by form and
does not test whether each node can be derived from its dependencies. Each line reports a clause
it finds false or underivable; N12 (the last link) is the first real test.

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

- Clearly above 30,000, sub-blueprint first: R05 (41–79k), R06 (39–75k), R10 (60–115k), R11 (32–62k),
  N04 (42–81k), N07 (35–66k).
- Above 30,000 only at the high ratio: R07 (27–51k), R09 (21–41k), R12 (29–56k), N01 (22–41k),
  N05 (26–50k), N06 (24–47k), N08 (21–40k).
- One line: S03, S04, S05, R08, W01, W02, W03, H01, H02, H03, N02, N03, N09, N10, N11, N12.

## Next

1. Lines on the 29 open nodes, one branch `line/<ID>` each (`docs/tasks/README.md`).
2. Module-system migration of the existing files on a branch, verified by CI.
3. `formalization.yaml`, `LICENSE`.
