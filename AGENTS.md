# ContinuousFlexibility

Lean 4 formalization of `thm:main` of the 62-page manuscript in
`paper/flexible-surface-rewrite/` (statement: `01-introduction.tex`, lines 18–31).
The endpoint is the unconditional theorem, with zero `sorry` and only the axioms
`propext`, `Classical.choice`, `Quot.sound`.

## Where things are

- `src/ContinuousFlexibility/` — Lean sources. `src/ContinuousFlexibility.lean` imports every finished module.
- `src/ContinuousFlexibility/Blueprint/` — the blueprint: one intermediate statement per file and the assembly theorem.
- `docs/STATUS.md` — the only progress ledger. `docs/tasks/` — one task file per open statement.
- `docs/archive/` — records of the earlier workflow; read-only history.
- `paper/` — manuscript. `vendor/` — third-party code, if any.

## How work is divided

- One blueprint statement is one line of work with its own files. Nobody needs approval to edit their own files.
- A task file states the problem, the completion standard and the source. Nothing else.
- A statement is finished when its `sorry` is replaced by a proof of the same statement, the module is in the root import, and CI is green. A weaker, relative or conditional version does not finish it.
- If a frozen statement turns out false or unusable, say so in `docs/STATUS.md` and fix the statement together with the assembly theorem.

## Rules

- `sorry` is allowed only in `src/ContinuousFlexibility/Blueprint/` statement files. The assembly theorem and every other module have none.
- No project axioms, `native_decide` or `unsafe`.
- Toolchain `leanprover/lean4:v4.35.0-rc3` and the mathlib revision in `lake-manifest.json` are fixed.
- Do not raise heartbeat limits. Find the slow declaration and fix it.
- Symmetric cases (left/right, the two endpoints) are one general lemma, not two copies. One object has one representation.
- One line normally carries a node of 20,000–30,000 lines. A node expected to go well beyond 30,000 lines gets its own sub-blueprint first.

## Reporting

- Report "modules compiled / total" and "statements open". Never report `sorry` counts or "only N blockers left".
- Check an estimate against data before stating it. A task at twice its estimated size is reported at once.

## Lean conventions

- Smoothness is `ContDiff ℝ ∞`; the top order in `ℕ∞ω` means analytic.
- `PolarPoint = ℝ × ℝ` has the max norm; Euclidean identities use explicit coordinate pairings.
- Do not assume a global real primitive of the polar connection on an annulus.
- Write explicit types on definitions. In module files use `_apply` lemmas for mathlib definitions, not `rfl`, `simp` or `change` through them.

## Building locally

- One importing module can take 3–4 GB. Check for running `lean` processes first and build single targets: `LEAN_NUM_THREADS=4 lake build <module>`.
- To check one file without writing artifacts: `lake env lean <file>`.
