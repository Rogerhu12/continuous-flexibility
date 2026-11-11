# Status

Last updated: 2026-11-11.

## Active line: N04Coordinates

The branch `line/N04Coordinates` and [PR #18](https://github.com/Rogerhu12/continuous-flexibility/pull/18)
retain the exact frozen theorem `N04bStatement → N04cStatement`. This statement is still open.

The source-pairing conjunct is proved by `Analysis.canonicalSource_pairing_of_partA`.
Reflection, angular equivariance, and the inverse identities identify the fundamental
open strip; a genuine Jacobian change of variables and null boundary lines then give
the required half-open-period integral. Its local axiom audit reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The analytic division lemmas use the actual Taylor remainder, rather than an
assumed quotient estimate. `CanonicalCubicPointwise` proves the formula for every
derivative and the bound `M / 6` on any closed nonnegative interval, with a fixed
loss of three derivatives. `CanonicalCubicMixed` differentiates the scaled
integral in both cylinder variables; `CanonicalCubicJets` applies that formula
to the radial quotient. All three vanishing boundary jets are explicit
hypotheses. The operator identity also determines the potential by testing the
constant function, and the positive-piece factorization uniquely determines
the divided coefficients in the open piece.

The additional proof modules isolate the remaining uniform jet estimate without
adding it to `N04bStatement`. `N04PartA` and `N04PartB` were moved verbatim to
`Blueprint/CanonicalParts.lean` and reexported by `Blueprint/Statements.lean`;
their content and the assembly theorem are unchanged. Normalization sets only
unused negative-piece divided coefficients and off-sector fields to zero.

The still-unproved clause is the bound on all mixed derivatives of the potential
and the three divided coefficients, on one neighborhood and with one fixed loss:

```lean
∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z ∈ U, ∀ m p,
  p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
    |mixedDerivative a b (K.potential z m) p| +
    |mixedDerivative a b (K.dividedDifference z m).a p| +
    |mixedDerivative a b (K.dividedDifference z m).b p| +
    |mixedDerivative a b (K.dividedDifference z m).c p| ≤
      B * T.E0 (T.sample (K.cell m)) ^ B *
        (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)
```

This cannot simply be extracted for an arbitrary qualitative witness. On a
negative piece the divided coefficient may be replaced by the unbounded angular
coordinate while preserving both qualitative parts. More substantially, the
positive-piece relation `F = d^3 * e` is asserted only where `d > 0`; any numerator
has that factorization there, so the relation does not assert the three vanishing
endpoint jets needed by cubic division. The paper obtains them from its actual
boundary-polynomial construction. A proof of the existential node must construct
quantitatively controlled coordinates and establish those endpoint identities.
The arbitrary-witness counterexample does **not** refute that existential node.

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
| Lean modules compiled / total | 382 / 390 |
| Modules in the root import | 340 |
| Lines of Lean under `src/` | 93,574 |
| Axiom audit (`lake build`, 3834 jobs) | passed: 11,293 declarations, 8,540 theorems |
| Blueprint statements proved / total | 13 / 42 (S01, S02, R01, R02, R03, R04, W01, N12, Tame, N04Cubic, R05a, N04Transmission, ScalarCalculus) |
| Challenge (`FlexibleSphere.exists_closedBending`) | not proved |
| Modules on the module system | 1 (the Challenge) of 394 |

These counts include main's completed N12 proof. The compiled count is the
source import closure of the four successful default targets; it excludes
stale artifacts restored from other branches. The 8 modules outside that
default build are unfinished files of the earlier workflow:
`Analysis.CircleJetEncoding`, `Analysis.CircleJetEvaluation`, `Analysis.PhysicalJetMollification`,
`Analysis.ProjectiveNewtonCommonOrbit`, `Analysis.ProjectiveNewtonParameterGrowth`,
`Radial.MorseChainPartitionTrace`, `Radial.MorseChainRealization`, `Radial.MorseChainSelectedJets`.

## What is proved

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
