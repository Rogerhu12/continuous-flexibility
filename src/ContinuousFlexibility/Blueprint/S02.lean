import ContinuousFlexibility.Statements.Milestones
import ContinuousFlexibility.Scalar.Determinant

/-!
# Blueprint node S02

Source: `paper/flexible-surface-rewrite/03-height-equation.tex` lines 47–115 (`eq:cart-determinant-identity`); `paper/flexible-surface-rewrite/03-height-equation.tex` lines 336–360 (`eq:cart-completed-normalized-derivative`).

Task file: `docs/tasks/S02.md`. The statement is frozen. Proved.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem S02 : S02Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r E w wr k p kr pr pt hr hD
    exact linear_determinant r E w wr k p kr pr pt hr hD
  · intro r E w wr k p kr pr pt hr hD hQ
    exact corrected_determinant r E w wr k p kr pr pt hr hD hQ
  · intro r E Er k p kr pr pt t h
    exact correctedAngular_of_residual_zero r E Er k p kr pr pt t h
  · intro r w wr
    refine ⟨heightDiscriminant_radial w, ?_, ?_, ?_⟩
    · simp [linearRadial, heightQ]
    · simp [linearMixed]
    · unfold linearAngular radialEnergy
      simp only [mul_one]
      apply congrArg (fun v : ℝ => v / r)
      ring

end ContinuousFlexibility.Blueprint

