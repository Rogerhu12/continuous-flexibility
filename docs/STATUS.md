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
| Blueprint statements proved / total | blueprint v2 not written yet |
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

The earlier statement layer (`Statements/`, 58 target propositions) has no assembly theorem:
nothing proves that those targets imply the main theorem. Blueprint v2 replaces it.

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

`.github/workflows/build.yml` is written and has never run: there is no GitHub remote yet.

## Next

1. Create the GitHub repository, push, get the first green CI run with cache.
2. Module-system migration of the existing files on a branch, verified by CI.
3. Blueprint v2: necessary intermediate statements in paper order as
   "for all inputs of the previous step there is the output of this step", proofs `sorry`,
   assembly theorem to the Challenge proved first.
4. `formalization.yaml`, `LICENSE`.
5. One task file per statement; start the lines.
