import ContinuousFlexibility.Analysis.N01cCoefficientTameBounds
import ContinuousFlexibility.Analysis.N01cCharacteristicSpeedTameBounds
import ContinuousFlexibility.Analysis.N01cOrdinaryFlowBounds

/-!
# N01c on a fixed primitive witness

This is the relative form of the three actual N01c factories. The
reference, material data, physical spaces, and control geometry are fixed
inputs. Only the common indices and radius are chosen, and the same
primitive certificate is returned beside the N01 conclusion.

This leaf targets the N01c parameter-order flow-loss interface. It does
not turn that interface into a loss uniform in the parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Blueprint

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
