import ContinuousFlexibility.Analysis.SolveCoupledSystem

/-!
# Blueprint node Solve

The Nash–Moser iteration with quadratic error (Theorem 9.4) applied to the coupled system: one solution at a nonzero parameter.

Source: `paper/flexible-surface-readable/09-solving-the-equation.tex` lines 251–413.

Task file: `docs/tasks/Solve.md`. The statement is frozen. The proof runs the
fixed-parameter iteration on the actual normalized sector and extracts its
nonzero-parameter zero using the N02/N08 realization identities.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem Solve (hN10 : N10Statement) (hTame : H01Statement ∧ H02Statement) : PointBranchStatement := by
  clear hTame
  obtain ⟨A, T, S, C, R, base, loss, ε, q0, hT, hS,
    L, K, Vol, b, Domain, Relative, G, P, B, N, V, Q, h09, h10⟩ := hN10
  have h1 := h09.1.1.1.1.1.1.1.1
  have h2 := h09.1.1.1.1.1.1.1.2
  have hG := h09.1.1.2.1
  have h8 := h09.1.2
  have h9 := h09.2
  have hsolution :=
    ContinuousFlexibility.Analysis.solve_coupled_exists_normalized_zero
      (D := A.val) (T := T) (S := S) (C := C) (R := R)
      (L := L) (G := G) (P := P) (B := B) (N := N) (V := V) (Q := Q)
      (base := base) (loss := loss) (ε := ε) (q0 := q0)
      hT hS h1 hG h8 h9 h10
  rcases hsolution with ⟨x, q, hq, hnear, hsector, hrow, hzero⟩
  exact pointBranchStatement_of_jointResidual_zero
    (A := A) (T := T) (S := S) (C := C) (R := R) (G := G) (P := P) (B := B)
    (base := base) (loss := loss) (ε := ε) (x := x) (q := q) hT hS h1 h2 h8
    hq hnear hsector hrow hzero

/--
info: 'ContinuousFlexibility.Blueprint.Solve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Solve

end ContinuousFlexibility.Blueprint
