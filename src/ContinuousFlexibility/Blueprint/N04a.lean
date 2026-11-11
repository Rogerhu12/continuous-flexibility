import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.N04SignedPieces
import ContinuousFlexibility.Analysis.N04CanonicalAtlas

/-!
# Blueprint node N04a

The physical positive and negative pieces and the reference Liouville atlas.
This proves the frozen geometric Part A, including closed-endpoint
regularity and the actual symmetry identities. The characteristic
Tricomi form is a further requirement in Part B.

Source: paper/flexible-surface-readable/07-fixed-geometry.tex,
lines 992–1046, 1211–1303, and 1316–1497.

Task file: docs/tasks/N04a.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem N04a (hN03 : N03Statement) : N04aStatement := by
  obtain ⟨A, T, S, C, R, L, base, loss, ε, hT, hS, h03⟩ := hN03
  have hgeom : RadialProfileGeometry A.val := A.property.1.choose_spec.1
  have hcontrols : controlGeometryConditions A.val S C := h03.1.1.2.2.2.1
  obtain ⟨P, hP, _⟩ := n04_exists_signed_pieces hgeom hcontrols
  refine ⟨A, T, S, C, R, L, n04CanonicalAtlas A.val S C L P,
    base, loss, ε, hT, hS, h03, ?_⟩
  exact n04CanonicalAtlas_partA hgeom hP

#print axioms ContinuousFlexibility.Blueprint.N04a

end ContinuousFlexibility.Blueprint
