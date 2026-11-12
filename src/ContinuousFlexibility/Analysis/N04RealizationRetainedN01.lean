import ContinuousFlexibility.Analysis.N04RealizationFlowInstallation
import ContinuousFlexibility.Analysis.N01cCoefficientTameBounds
import ContinuousFlexibility.Analysis.N01cCharacteristicSpeedTameBounds
import ContinuousFlexibility.Analysis.N01cOrdinaryFlowBounds

/-!
# Completing N01 on the retained input data

The relative N01c assembly is the existing fixed-witness recovery proof.
The wrapper installs one actual flow family, then keeps the supplied
reference, material data, physical spaces and all six static geometry
fields through the three quantitative factories. Retained reference
metadata remains attached to the unchanged caller-supplied reference.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Blueprint

/-- The actual coefficient, speed and flow factories retain their input
records; only the common neighborhood and derivative losses are chosen. -/
theorem n01Primitive_exists_fixedWitness_properties
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base' loss : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
        N01Properties D T S C base' loss ε' ∧
          N01PrimitiveGeometry D T S C := by
  obtain ⟨b₀, l₀, hb₀, hcoeff₀⟩ :=
    n01_coefficientFamilyTameBounds_of_localization
      hS hT hA hε hB hE hG.1 hG.2.1
  have hε₀ : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  have hB₀ : N01PartB D S C b₀ (min ε (1 / 2)) :=
    n01PartB_mono hB hb₀ (min_le_left _ _)
  obtain ⟨b₁, l₁, ε₁, hε₁, hb₁, _, hε₁ε, hB₁, hcoeff₁, hspeed⟩ :=
    n01_exists_common_characteristicSpeedTameBounds
      hS hT hA hε₀ hB₀ hcoeff₀ hE hG.1 hG.2.1 hG.2.2
  obtain ⟨b₂, ε₂, hb₂, hε₂, hε₂ε, hflows⟩ :=
    n01_exists_ordinaryFlowFamilyTameBounds hS hT hA hε₁ hB₁ hG hE hspeed
  refine ⟨b₂, l₁, ε₂, hb₀.trans (hb₁.trans hb₂), hε₂,
    hε₂ε.trans (hε₁ε.trans (min_le_left _ _)), ?_, hG⟩
  exact n01Properties_of_parts hA hε₂ (n01PartB_mono hB₁ hb₂ hε₂ε)
    (coefficientFamilyTameBounds_mono_of_accumulatingProfile hT hA.1.1
      hcoeff₁ hb₂ le_rfl hε₂ε) hflows

end ContinuousFlexibility.Statements

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
