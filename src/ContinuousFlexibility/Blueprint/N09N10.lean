module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Analysis.CoupledStagesConstruction
public import ContinuousFlexibility.Analysis.CoupledCircleChartSmooth
public import ContinuousFlexibility.Analysis.CoupledCircleErrorSmooth

/-!
# Blueprint node N09N10

The approximate right inverse of the coupled system and the exact quadratic error identity.

Source: `paper/flexible-surface-readable/09-solving-the-equation.tex` lines 189–251; `paper/flexible-surface-readable/09-solving-the-equation.tex` lines 299–346.

Task file: `docs/tasks/N09N10.md`. The proof retains the frozen statement.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N09N10 (hN08 : N08Statement) (hTame : H01Statement ∧ H02Statement) : N10Statement := by
  obtain ⟨A, T, S, C, R, L, K, Vol, b, Domain, Relative, G, P, B,
    base, loss, ε, hT, hS, h08⟩ := hN08
  have h1 : N01Properties A.val T S C base loss ε := h08.1.1.1.1.1.1.1
  have h2 : N02Properties A.val T S C R base ε := h08.1.1.1.1.1.1.2
  have hD : IsAccumulatingProfile A.val := h1.1.1
  obtain ⟨base', ε', q0, h10⟩ :=
    coupled_nonlinearStagesThrough10_of_circle_calculus hT hS h08
      (coupled_chartIncrement_smoothTameOn hD hT hS h1 h2)
      (coupled_returnError_smoothTameOn hD hT hS h1 h2)
  exact ⟨A, T, S, C, R, base', loss, ε', q0, hT, hS, h10⟩

#print axioms N09N10

end ContinuousFlexibility.Blueprint
