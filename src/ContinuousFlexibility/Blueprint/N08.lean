module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Analysis.N08Assembly
public import ContinuousFlexibility.Analysis.N08CircleUniform
public import ContinuousFlexibility.Analysis.N08ParameterRestriction

/-!
# Blueprint node N08

The joint residual of height and circle equations and its control columns.

Source: `paper/flexible-surface-rewrite/09-solving-the-equation.tex` lines 13–137.

Task file: `docs/tasks/N08.md`. The actual residual, control columns, and
uniform diagonal are assembled on one common neighborhood. All previous
stages retain the same reference, physical spaces, and scalar inverse.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N08 (hN07 : N07Statement) (hS04 : S04Statement) : N08Statement := by
  obtain ⟨A, T, S, C, R, L, K, Vol, b, Domain, Relative, G, base, loss, ε,
    hT, hS, h07⟩ := hN07
  have hN : N01Properties A.val T S C base loss ε := h07.1.1.1.1.1.1
  have hReturn : N02Properties A.val T S C R base ε := h07.1.1.1.1.1.2
  obtain ⟨diagonalBase, diagonalRadius, _, hdiagonalRadius, _, hdiagonal⟩ :=
    n08CircleDiagonal_uniform hT hS hN hReturn
  obtain ⟨newBase, newLoss, η, hbase, hloss, hη, hηε, Joint, Columns, h08⟩ :=
    n08Properties_of_uniform_diagonal hT hS hN hReturn h07.2.1
      hdiagonalRadius hdiagonal
  exact ⟨A, T, S, C, R, L, K, Vol, b, Domain, Relative, G, Joint, Columns,
    newBase, newLoss, η, hT, hS,
    n08_through07_mono hT h07 hbase hloss hη hηε, h08⟩

#print axioms N08

end ContinuousFlexibility.Blueprint
