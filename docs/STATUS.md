# Status

Last updated: 2026-11-11.

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
| Lean modules compiled / total | 319 / 327 |
| Modules in the root import | 319 |
| Lines of Lean under `src/` | 87,633 |
| Axiom audit (`lake build`, 3751 jobs) | passed: 10,671 declarations, 8,043 theorems |
| Blueprint statements proved / total | 7 / 42 (S01, S02, R01, R02, R03, R04, W01) |
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

Open nodes (35): ScalarCalculus, ScalarWeighted, Tame, Spaces, R05a, R05b, R06a, R06b, R06c, R07, R08,
R09, R10a, R10b, R11a, R11b, R12, N01a, N01b, N01c, N02N03, N04Root, N04Cubic, N04Transmission, N04a,
N04b, N04Coordinates, N05, N06, N07a, N07b, N08, N09N10, Solve, N12.

Tool tasks (5), abstract lemmas that the manuscript isolates and that have no blueprint node; their
Lean statements follow the manuscript and are not frozen: Tool-OneHighFactor (Lemmas 7.2, 7.3),
Tool-AngularCommutator (Lemma 8.4), Tool-SobolevExtension (extension operator, three-lines lemma),
Tool-R10a-Inner (Lemma 6.3), Tool-R10a-Outer (Lemmas 6.4, 6.5).

One task file each in `docs/tasks/` (40 in total).

Whether each node can be derived from its hypotheses is tested by its line; `N12` and `Solve`
are the first real tests of the chain. `R10a` has one frozen statement for the inner and the outer
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

## Next

1. Lines on the 35 open nodes and 5 tool tasks, one branch `line/<Task>` each (`docs/tasks/README.md`).
2. Module-system migration of the existing files on a branch, verified by CI.
3. `formalization.yaml`, `LICENSE`.
