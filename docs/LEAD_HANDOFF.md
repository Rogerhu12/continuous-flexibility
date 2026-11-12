# Lead handoff (2026-11-12 22:55 Beijing time)

The previous lead session became error-prone after a very long run and handed over. This file is
the lead's working notes; `docs/STATUS.md` stays the only progress ledger. Delete this file once
everything below is done or moved.

## Where things stand

- `main` (`ecd4e991`): 37 / 42 blueprint statements proved. Open: N01c, N02N03, N04b,
  N04Coordinates, N05.
- **N01c (PR #23, ready, head `bb419aa4`) and N05 (PR #35, ready, head `a79ed3f6`)** are proved
  and green. Together they passed integration (`integrate/batch-12`, run 43217283062, both
  builds reused from the lines' artifacts). Merging with current `main` then conflicted:
  N06 (already on main) had copied 15 of N05's files `Analysis/N05*.lean` and changed them.
  Two integration builds are running:
  - `integrate/batch-13a` = batch-12 + main, the 15 files in **N05's** versions;
  - `integrate/batch-13b` = the same, the 15 files in **main's (N06's)** versions.
  Workflow conflict resolved as main's version. Push the first green one to `main` (check that
  `line/N01c` and `line/N05` heads did not move), then update STATUS (39 / 42) and record the
  statement repairs below. If both fail, read the errors: the losing side's proof uses the other
  version of those files.
- Statement repairs to record in STATUS when N01c/N05 land (decided by the lead; the user
  delegated statement decisions): N01c changes the flow-loss quantifier order in `N01Properties`
  (manuscript §7 lines 222–230, 768–806), and adds `N01PrimitiveGeometry` /
  `N01RadialPrimitiveGeometry` (in `Blueprint/Statements.lean`, `Statements/RadialTargets.lean`)
  to the N01a output; N01a's proof on main was ported to provide them. N05 adds the same two
  definitions. Details: PR #23 description, `docs/N01c-loss-audit.md`, `docs/N01c-geometry-audit.md`.
- **N02N03 (PR #21, draft)**: the node theorem compiles; the remaining work is compile errors in
  the `Analysis/N01Correction*` chain (definitional unfolding of `lp`/`PreLp`/`WithLp` structures
  hits the 200000 heartbeat limit). The lead fixed `N01CorrectionCoefficientFlatBounds` line 145
  (commit `f4918031`); the line itself fixed that file's timeouts by stating the bound as a
  general lemma over an abstract `E`/`A` (`correctionCoefficient_local_bounds_of_sublevels`).
  Current blocker: `N01CorrectionCoefficientTameTransfer.lean` line 48, theorem
  `N01Properties.returnCorrectionCoefficientScalarJets_flat_bound_of_joint_growth`, `whnf`
  heartbeat timeout for the whole declaration (~50 s). Likely fix: the same abstraction
  (prove it for abstract towers and jets, then instantiate). The lead claimed this file and
  `N01CorrectionCoefficientStripJets` on PR #21; the line session is active and pushes often.
- **N04b (PR #34, draft)**: all sub-statements proved, CI red, has not merged main, so it still
  uses the old CI workflow (slow). PR comment asked it to merge main.
- **N04Coordinates (PR #18, draft)**: merged main; sub-statement `Blueprint/N04Coordinates/Realization`
  still has `sorry`.

## CI (all on `main`, `.github/workflows/build.yml` and `probe.yml`)

- A run uses the workflow file of its own branch: lines get improvements only after merging main.
- Cache layers: main's newest entry first, then the branch's own entry on top (line branches).
  GitHub lets a ref read only its own caches and main's.
- Main and `integrate/*` reuse each merged line's build through the artifact `lake-build-line`
  (uploaded by every non-cancelled line run; only green runs are reused), found from
  `Merge line/X (sha)` commit subjects. Worked in batch-12.
- Line branches: quick check of changed modules first (stops on the first failure), a watchdog
  stops any changed file compiling for more than 300 s (`FILE_LIMIT_SECONDS`), every run prints
  the 15 slowest modules.
- Cache save happens before deleting older entries (`c070da70`); the old order lost
  N02N03's cache once.
- `probe.yml`: `gh workflow run probe.yml --ref line/X -f probes=probe/X -f variants='["v1","v2"]'
  -f file=<path>` runs one job per variant directory `probes/<v>/` of branch `probe/X` on the line's
  branch, reading its cache, and checks one file with `lake env lean`. Do **not** push to the
  line branch while a probe runs: the new run's partial cache can be restored by the probe.
  `count_heartbeats in` failed to parse in the last attempt; untested otherwise.
- 13 ghost runs from 2026-11-12 04:50 show as queued with 0 jobs and cannot be cancelled.

## How the lead works here

- Merge authority: merge ready PRs after CI-green integration; statement-layer repairs are the
  lead's decision, recorded in STATUS (original clause, reason, new clause).
- Integration: `scripts/integration/merge_lines.sh <Task>...` (always `--no-ff`), dispatch
  `build.yml` on an `integrate/*` branch, push to `main`, update STATUS.
- Before acting on a class of things (CI runs, lines, branches) list every state and branch.
  Verify platform behaviour before building on it; test workflow changes on one module first
  (playbook §7: `C:\Users\Boyang\Downloads\FORMALIZATION_PLAYBOOK.md`).
- Digest: report only events (PR ready or merged, new claims, draft lines silent for 60 minutes,
  cancelled old-workflow runs). The previous session's watcher lived in its scratchpad and is gone.
- Quiet hours 04:30–07:30 Beijing time: no work. The user gets up at 10:00: one summary then.
- Reply in Chinese, Beijing time. Prompts for the user's Pro sessions carry the real token the
  user gives in chat, never a placeholder; never write tokens into the repository (it is public).
- Lines that finish move to the six reserved topics of `Rogerhu12/math-research`
  (`docs/tasks/README.md`, "When you finish", step 4). `primes-n2-plus-1` is shelved; the other
  five were still 待领 at the handover.

## Not done (playbook items)

- Module system (only 7 of 3,011 files), `formalization.yaml`, `LICENSE`.
- PRs far above ~100 modules (N01c 1,152 before cleanup, N06 715, N04Coordinates 649).
