import ContinuousFlexibility.Blueprint.R10a.Regional
import ContinuousFlexibility.Blueprint.R10a.Poisson

/-!
# Blueprint node R10a

At every even frequency: the inner inverse, the outer inverse, their Poisson functions and the selected margin on one geometry.

Source: `paper/flexible-surface-rewrite/06-global-reference-inverse.tex` lines 231–522.

Task file: `docs/tasks/R10a.md`. The frozen statement is assembled from
the parameterized geometry, actual regional data, and Poisson correction.
The regional construction remains an open sub-blueprint task.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem R10a (hR06 : R06Statement) (hR07 : R07Statement) (hR08 : R08Statement) (hR09 : R09Statement) : R10aStatement := by
  obtain ⟨D, hD, hB, hconstruction, hregional⟩ := R10aRegional hR06 hR09 (R10aGeometry hR06)
  refine ⟨D, hD, hB, hconstruction, ?_⟩
  intro j hj heven
  obtain ⟨W, hfrequency⟩ := hregional j hj heven
  obtain ⟨M, hM, hpieces⟩ := R10aPoisson hD hB W
  exact ⟨M, hM.trans hfrequency, hpieces⟩

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R10a
