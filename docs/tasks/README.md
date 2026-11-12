# Working on a blueprint node

Each file `docs/tasks/<Node>.md` is one line of work: problem, completion standard, source.
A `Tool-*` task has no blueprint node: its Lean statement follows the manuscript lemma it cites.
Line numbers refer to the readable manuscript in `paper/flexible-surface-readable/`; older Lean files
cite the 62-page version in `paper/flexible-surface-rewrite/`, which has the same labels.
One line works on one branch `line/<Node>` and opens one pull request into `main`.
The rules below are the same for every line.

## Notices to individual lines

Read this section every time you check the rules. A notice is removed when it is done.

- **All lines: merge `origin/main` to get the quick check and the 5-minute file limit.** CI first
  builds only the modules your branch changed and stops at the first failure, so errors return in
  minutes; the full build runs only when that passes. A changed file that compiles for more than
  5 minutes is stopped and named in the log: split it, or find the slow declaration. Each run prints
  the 15 slowest modules it compiled.
- **All lines: merge `origin/main` now to get the faster CI.** A run uses the workflow file of the
  branch it runs on. The workflow on `main` (since `4c5e7aff`) first restores main's compiled build
  and then your branch's own, so after merging main you no longer recompile what main already
  compiled (N07a, N07b, R11a, N08: well over 100,000 lines). A branch without this merge rebuilds
  all of it on every push; N02N03's current run has been compiling for more than 1.5 hours.
- **N02N03, N04b, N04Coordinates, N05, N06: merge `origin/main` now.** N07b's statement repair is on
  `main` (`docs/STATUS.md`, "Statement repairs"): `physicalPieceOpen` takes the state, the old fixed
  interval is `referencePhysicalPieceOpen`, and the N04 output also carries
  `CanonicalPrimitiveGeometry`, which the N04 producers must prove. N07a's repair is now on `main`
  too: N02N03 must also prove `ReturnCorrectionSpatialProperties` (smoothness and π-periodicity of
  the actual corrected `b/c` coefficients), and the N04 producers also
  `CanonicalGeometry.PrimitiveGeometryProperties`. One more will follow (N01c:
  `N01PrimitiveGeometry` in the N01a output and new flow-loss quantifiers). Merge `main` each time
  one lands.
- **R10a, R11a, N07a, N07b, N09N10: your math-research access check was wrong, not your access.**
  `git ls-remote` on a bare URL has no credentials. Use the URL derived from your `origin` remote
  (step 4 of "When you finish" below), and take the next reserved topic.
- **N01a (PR #31): do not mark ready yet; merge `origin/main` and port to R12's definitions.**
  R12 (merged) changed two definitions in `Statements/Radial.lean`:
  `RadialCellIntegrable D f` is now `∀ m, MemLp (fun x => D.localizer m x.1 * f x) 2
  (radialPhysicalMeasure D)`, and the first-normal estimate takes `SourceDerivativeMember D γ M fθ`
  instead of `SourceMember D γ M (fθ, 0)`. R12 also added declarations with the names of six of
  yours in `ContinuousFlexibility.Statements`. Branch `integrate/batch-7` already contains two
  fixes you can merge: the six clashing names renamed `n01a_*`, and the argument in
  `N01aReferencePureRow.lean`. The next error is `N01aReferenceMeasure.lean:40`
  (`integrable_square` becomes `(hf m).integrable_sq`); the places that construct
  `RadialCellIntegrable` (`n01a_radialCellIntegrable_sub`, `cell_integrable_iff`, ...) need
  `memLp_two_iff_integrable_sq` with the measurability you already assume. Mark ready again when
  CI is green on the merge with current `main`.
  Since then N01b (merged) also changed `controlGeometryConditions` (`Statements/Nonlinear.lean`):
  the control support clause is now `tsupport (C.control m) ⊆ Ioo (C.left m) (C.right m)`, so the
  controls N01a constructs must satisfy the strict inclusion.

## Start

Read `AGENTS.md`, `docs/STATUS.md`, your task file, your node file
`src/ContinuousFlexibility/Blueprint/<Node>.lean`, the definition of the statement under
`src/ContinuousFlexibility/Statements/` or in `Blueprint/Statements.lean`, the cited manuscript lines, and the existing modules
that already prove parts of it. Search `src/` thoroughly: much may exist. Six nodes were closed
in minutes because a theorem with exactly the node statement was already in the tree.

Work until the completion standard is fully met. Do not stop at a draft or an interim report.
Push often.

## The rules change: check them often

The rules are this file and `AGENTS.md` **on `main`**. The lead updates them while lines work, and
the copy on your branch is the one from when you branched, so it goes stale. The version on `main`
always wins. Check for changes before each push, and at least once an hour (git only, no API quota):

```bash
git fetch -q origin main && git log --oneline HEAD..origin/main -- docs/tasks/README.md AGENTS.md
```

If it prints anything, read the current rules and follow them from then on:

```bash
git show origin/main:docs/tasks/README.md
```

```bash
git show origin/main:AGENTS.md
```

## What you edit

- Your node file.
- New files you create. Proofs go in new modules under `src/ContinuousFlexibility/<Area>/`
  with distinctive names; sub-blueprint statements go in `src/ContinuousFlexibility/Blueprint/<Node>/`.
- Existing files of other areas only when the proof needs a change there; say so in the pull request.
  Before changing or generalizing an existing file, merge `origin/main` and search it for the lemma:
  three lines once proved the same ODE lemma in the same file under three names, and every copy
  became a merge conflict. Give a new declaration a name that is not used anywhere in `src/`.
- **Not** `src/ContinuousFlexibility.lean` and **not** `docs/STATUS.md`. The root import is generated
  by `scripts/gen_root.py` from every `.lean` file under `src/ContinuousFlexibility/` (outside
  `Blueprint/`), in CI and before local builds; the ledger is kept by the lead. Report your numbers
  in the pull request instead. Editing these two files only causes merge conflicts.
- Because every file is built, every `.lean` file you push must compile. Keep unfinished drafts out
  of `src/` (for example in a `drafts/` directory at the repository root, which nothing builds).

## If the node is large

A line normally carries a whole node; 20,000–30,000 lines of Lean in one line is expected.
Only if the node will clearly go well beyond 30,000 lines, write a sub-blueprint first:

- the necessary intermediate statements in manuscript order, each a `theorem ... := by sorry`
  with real definitions, in its own file under `Blueprint/<Node>/`, each of a size one line can
  carry (up to about 30,000 lines), each with a task file `docs/tasks/<Node>-<name>.md`;
- replace the `sorry` in your node file by a sorry-free proof that assembles the node from those
  statements and the node's hypotheses, and push that first so other lines can take the pieces;
- then prove the sub-statements.

Symmetric cases (the two endpoints, left and right) are one general lemma.

## Building

```bash
lake exe cache get
```

```bash
bash scripts/get_build_cache.sh
```

The second command restores the compiled project modules of `main`, so only your files compile.
Before building the root library locally, generate the root import:

```bash
python3 scripts/gen_root.py
```

Build single targets, never a bare `lake build` in a small sandbox:

```bash
LEAN_NUM_THREADS=2 lake build ContinuousFlexibility.Blueprint.<Node>
```

Check one file without writing artifacts with `lake env lean <file>`.

## If the sandbox cannot compile, use CI

Do not spend time fighting the sandbox. If a compile runs out of memory, is killed, or takes more
than a few minutes for one file, stop compiling locally: write the code, push, and read the result
of CI. That loop always works.

- CI builds everything once per push to a `line/**` branch (your pull request shows the checks of
  its head commit) and prints the blueprint status. Each branch keeps its own build cache, so a run
  takes about 2 minutes plus the time to compile what you changed. A newer push cancels the older run.
- See the CI result of your pull request (this uses GraphQL, which does not spend the REST quota
  below):

```bash
gh pr checks <PR-number>
```

- When it failed, find the run and read its errors once:

```bash
gh run list --branch line/<Node> --limit 3
```

```bash
gh run view <run-id> --log-failed
```

- The step "Build every library" prints every `error:` line with the following 60 lines; the full
  log is the artifact `build-log`.
- Push small, complete steps (one file or one lemma group at a time), so that one CI round tells
  you about one change.
- **Hard limit: your branch may be at most 20,000 added lines of Lean ahead of its last commit that
  passed CI.** A line can repair a few tens of thousands of uncompiled lines; beyond that the errors
  pile up faster than they are fixed. When you reach the limit, stop writing new material and make
  CI green first. Check the distance with:

```bash
git diff --shortstat $(gh run list --branch line/<Task> --status success --limit 1 --json headSha --jq '.[0].headSha') HEAD -- '*.lean'
```

  Code that does not compile is not progress: the further a branch runs ahead of a green build,
  the more layered its errors become.

## GitHub API quota

All lines share one GitHub account, and with it one REST quota of 5,000 requests per hour. When it
is used up, every `gh` command of every line fails with `API rate limit exceeded` for up to an hour.

- Never run `gh run watch`: it polls every 3 seconds, about 1,200 requests an hour.
- Never poll in a loop. Wait at least 5 minutes after a push, then check at most once a minute.
- Check CI with `gh pr checks` (GraphQL, a separate quota), not with repeated `gh run list` or
  `gh run view`.
- Download a failed log once per run and keep it in a file.
- List branches with `git ls-remote`, which uses no API quota.
- If a command reports `API rate limit exceeded`, do not retry. Keep writing and checking code
  locally; this shows when the quota resets (it does not count against the quota):

```bash
gh api rate_limit --jq '.resources.core.reset | todate'
```

## Lean

- Toolchain and mathlib are fixed. `Set.mem_setOf_eq` and `push_neg` are deprecated in this mathlib.
- Use plain `import` headers (no `module` keyword) until the module migration is merged.
- Do not raise heartbeat limits; find the slow declaration.

## Claiming a task

A task is taken when the branch `line/<Task>` exists on GitHub. Nothing else records a claim.

```bash
git ls-remote --heads origin "line/*"
```

To claim a task, create its branch from `main` and push it at once, before doing any work:

```bash
git fetch origin && git switch -c line/<Task> origin/main && git commit --allow-empty -m "Claim <Task>" && git push -u origin line/<Task>
```

If the push is rejected because the branch exists, someone else has the task: pick another.
Then open a draft pull request into `main` titled `<Task>`.

## When you finish

1. Merge the current `origin/main` into your branch, push, and wait until CI is green on that
   merge. Other lines land on `main` every hour; a branch that was green before can clash with
   them (two declarations of the same name, a changed shared file). Then mark your pull request
   ready for review and write the final report in it.
2. Take the next task that nobody has: the first one in the list "Pick next" of `docs/STATUS.md`
   whose branch does not exist. Claim it as above and continue. Do not wait for a review.
3. If your own task turned out to need a sub-blueprint, its pieces go to the top of the candidates:
   push the sub-blueprint first, so that they can be claimed.
4. **If every task here has a branch, switch to the research repository `Rogerhu12/math-research`.**
   The author has reserved six topics there for sessions that finish here. Take the first of them,
   in this order, whose row in `QUEUE.md` still says 待领:
   `topics/primes-n2-plus-1`, `topics/primes-4x3-27y2`, `topics/hodge-abelian-varieties`,
   `topics/abelian-surface-torsion-uniform`, `topics/selberg-eigenvalue-conjecture`,
   `topics/ramsey-r55`.
   - You have access with the credentials you already push with. Reuse them: derive the
     math-research URL from your `origin` URL, which carries them, instead of typing a bare URL (a
     bare URL has no credentials and fails with "could not read Username"):
     `MR=$(git remote get-url origin | sed 's#continuous-flexibility#math-research#')`, then
     `git ls-remote "$MR" HEAD` and `git clone "$MR"`. Never print `$MR` or write it to a file.
     Only if that fails too, write the exact error at the end of your pull request's final report.
   - Clone it with that URL and pull `main`. Read its root `README.md` in full, including the authorization section
     and every rule, and the topic's `README.md`. Change the topic's row in `QUEUE.md` to
     进行中（会话名/日期）, push, and start the research. From then on follow that repository's rules,
     not these.
   - Keep going until the completion standard in the topic's `README.md` is met. Do not stop at a
     stage report, an intermediate result or a "suggested next step" to wait for a reply; reaching a
     time limit is not a reason to stop. When a subproblem is done, take the next one in the topic's
     `open.md`. Wrap up only when the topic is truly complete or the conversation is close to its
     length limit, and update `HANDOFF.md` before you wrap up.
   - Never write a token into any file, commit, log, HANDOFF or note, and never repeat it in a reply.
     Do not upload PDFs, do not render pages as images, keep each file under 5 MB.

## Final report in the pull request

1. Is `theorem <Node>` sorry-free, and what does `#print axioms` show?
2. If not closed: the sub-statements introduced and which are proved.
3. Any clause of the frozen statement found false or underivable from its hypotheses, quoted exactly.
