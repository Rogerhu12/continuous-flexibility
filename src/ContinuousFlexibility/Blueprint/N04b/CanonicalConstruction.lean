import ContinuousFlexibility.Blueprint.Statements
import ContinuousFlexibility.Analysis.N04bFieldRegularity

/-!
# N04b: canonical coordinates of the actual corrected field

Construct the travel coordinates from the corrected characteristic flows,
split the physical component at its actual middle travel level, and use
the regularized root coordinates and the actual density height gauge.
The resulting domains may depend on the state; the canonical intervals
and the cut radius remain fixed.

The input consists only of the cumulative N01--N03 construction and raw
coefficient regularity, type, and its actual radial reference flow.
Every chart, closed inverse, partition,
operator identity, cut transmission identity and positive divided
difference is a conclusion.
Source: paper/flexible-surface-readable/07-fixed-geometry.tex, lines 992--1303.
Task: docs/tasks/N04b-CanonicalConstruction.md.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N04bCanonicalConstruction
    (A : RadialReference) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (base loss : ℕ) (ε : ℝ)
    (hT : IsMaterialData A.val T) (hS : IsPhysicalSpaces A.val T S)
    (h03 : NonlinearPropertiesThrough03 A.val T S C R L base loss ε)
    (hfield : N04bFieldRegularity A.val S C L base ε) :
    ∃ K : CanonicalData S,
      N04PartA A.val S C K base ε ∧ N04PartB S C L K base ε := by
  sorry

end ContinuousFlexibility.Blueprint
