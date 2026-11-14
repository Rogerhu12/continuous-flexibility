import ContinuousFlexibility.Analysis.N04RealizationFlowInstallation
import ContinuousFlexibility.Analysis.N01PrimitiveFixedWitnessConstruction

/-!
# Completing N01 on the retained input data

The relative N01c assembly uses the shared fixed-witness construction.
The wrapper installs one actual flow family, then keeps the supplied
reference, material data, physical spaces and all six static geometry
fields through the three quantitative factories. Retained reference
metadata remains attached to the unchanged caller-supplied reference.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

/-- The ordinary-flow installation changes only the three flow fields.
The original primitive support and lower-bound certificate and all six
static fields belong to the same completed N01 witness. -/
theorem n04Realization_retainedN01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r : ℝ, 1 ≤ T.E0 r) :
    ∃ Θ : (AnnularState S × ℝ) → ℕ → ℝ → ℝ → ℝ,
      ∃ base loss : ℕ, ∃ ε : ℝ, 4 ≤ base ∧ 0 < ε ∧
        N01Properties D T S (circleFlowGeometry C Θ) base loss ε ∧
        N01PrimitiveGeometry D T S (circleFlowGeometry C Θ) ∧
        (circleFlowGeometry C Θ).control = C.control ∧
        (circleFlowGeometry C Θ).cell = C.cell ∧
        (circleFlowGeometry C Θ).left = C.left ∧
        (circleFlowGeometry C Θ).right = C.right ∧
        (circleFlowGeometry C Θ).travel = C.travel ∧
        (circleFlowGeometry C Θ).referenceState = C.referenceState := by
  obtain ⟨Θ, ε₀, hε₀, hB⟩ := exists_n01b_circleFlowGeometry hT hS hA
  have hA' : N01PartA D T S (circleFlowGeometry C Θ) := circleFlowGeometry_partA hA Θ
  have hG' : N01PrimitiveGeometry D T S (circleFlowGeometry C Θ) := hG
  obtain ⟨base, loss, ε, hb, hε, _, hN, hPrimitive⟩ :=
    n01Primitive_exists_fixedWitness_properties hS hT hA' hε₀ hB hG'
      (fun r _ => hE r)
  exact ⟨Θ, base, loss, ε, hb, hε, hN, hPrimitive,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end ContinuousFlexibility.Analysis
