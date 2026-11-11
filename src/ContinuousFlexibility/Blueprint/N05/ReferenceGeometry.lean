import ContinuousFlexibility.Analysis.N05ReferenceInterface

/-!
# N05: selection of controlled reference coordinates

Source: readable manuscript §7, lines 462--715, and §8, lines 34--167.
Task: `docs/tasks/N05-ReferenceGeometry.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

/-- Select actual controlled reference charts while retaining the entire
preceding nonlinear construction. The final N05 hypothesis is unchanged. -/
theorem N05ReferenceGeometry (hN04 : N04Statement) :
    ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
      ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
        ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
          ∃ base loss : ℕ, ∃ ε : ℝ,
            IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
              NonlinearPropertiesThrough04 A.val T S C R L K base loss ε ∧
                N05ControlledReferenceCoordinates A.val S C K := by
  sorry

end ContinuousFlexibility.Blueprint
