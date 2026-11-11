import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.PointSolutionCore
import ContinuousFlexibility.Analysis.StateControlCofiniteClosure

/-!
# Blueprint node N12

The flat annular core from one solution at a nonzero parameter.

Source: `paper/flexible-surface-readable/10-endpoint-and-sphere.tex` lines 304–430.

Task file: `docs/tasks/N12.md`. The statement is unchanged. The control profile
has a smooth extension by the cofinite jet argument; the weighted height has
the global smooth extension provided by W03. The geometric construction then
uses only the scalar equation and the normalization at the chosen nonzero
parameter. The scalar identities it needs are already proved in the tree,
so the S03 hypothesis is not needed by this proof.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N12 (hBranch : PointBranchStatement) (hW03 : W03Statement) (hS03 : S03Statement) : N12Statement := by
  clear hS03
  obtain ⟨A, T, S, hT, hS, C, R, base, loss, ε, hN, x, q,
    hq, hnear, hsector, hrow, hscalar, _, _⟩ := hBranch
  exact nonempty_flatAnnularCore_of_point_smooth hN hS hq hnear hsector hrow hscalar
    (contDiff_stateProfile_of_n01 hS hT hN x)
    (((hW03 A.val T S hN.1.1 hT hS).1 (3 / 4 : ℝ) (by norm_num) x.1.1).1)

/--
info: 'ContinuousFlexibility.Blueprint.N12' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms N12

end ContinuousFlexibility.Blueprint
