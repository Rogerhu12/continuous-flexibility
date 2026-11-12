import ContinuousFlexibility.Analysis.N05PrimitiveReferenceAssembly

/-!
# N05 reference geometry from the primitive interface

The sub-statement retains every witness of the supplied N04 output.
Both primitive certificates are retained on the same canonical data.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N05ReferenceGeometry (hN04 : N04Statement) :
    ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
      ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
        ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
          ∃ base loss : ℕ, ∃ ε : ℝ,
            IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
              NonlinearPropertiesThrough04 A.val T S C R L K base loss ε ∧
                N05ControlledReferenceCoordinates A.val S C K := by
  obtain ⟨A, T, S, C, R, L, K, base, loss, ε, hT, hS, h⟩ := hN04
  exact ⟨A, T, S, C, R, L, K, base, loss, ε, hT, hS, h,
    n05_controlledReferenceCoordinates_of_primitive A.property.1 hT h⟩

/-- info: 'ContinuousFlexibility.Blueprint.N05ReferenceGeometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms N05ReferenceGeometry

end ContinuousFlexibility.Blueprint
