import ContinuousFlexibility.Analysis.N03NegativeInteriorFlows
import ContinuousFlexibility.Analysis.InteriorFlowTransport
import ContinuousFlexibility.Analysis.CanonicalCutFullFaithfulness

/-!
# The existing negative coordinates from an actual interior inverse flow

The whole-component transport equation, including the two cut axes,
comes from the actual N03 trajectories and the genuine first jets of
the canonical charts. It identifies the existing first integral with
its value on a fixed section transported by the constructed inverse
flow. No parameter regularity of the stored N03 flow is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem canonicalGluedAiryIntegral_eq_interiorFlowInverse
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {a b ρ : ℝ} (ha : C.left m < a) (hab : a < b) (hb : b < C.right m)
    (hρ : 0 < ρ) (plus : Bool)
    {Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (interiorScalarFlowField
        (interiorLocalizedSpeed hab.le hρ (negativeCharacteristicField plus (L.coefficients z)))
          a b) Θ)
    (hinverse : ∀ v θ, Θ v 1 (Ψ v 1 θ) = θ)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    canonicalGluedAiryIntegral S K z m (if plus then -1 else 1) (r, θ) =
      canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)
        (a, Ψ (interiorEndpointParameter a b r) 1 θ) := by
  let U : PolarPoint → ℝ :=
    canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)
  let f : PolarPoint → ℝ :=
    interiorLocalizedSpeed hab.le hρ (negativeCharacteristicField plus (L.coefficients z))
  have hsub : Icc a b ×ˢ (univ : Set ℝ) ⊆
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    fun q hq => ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt hb⟩, mem_univ _⟩
  have hU : ContDiffOn ℝ 1 U (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
    contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m (if plus then -1 else 1)
  have hUd (s : ℝ) (hss : s ∈ Icc a b) (η : ℝ) :
      DifferentiableAt ℝ U (s, η) :=
    ((hU (s, η) (hsub ⟨hss, mem_univ _⟩)).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hsub ⟨hss, mem_univ _⟩))).differentiableAt_one
  have htransport (s : ℝ) (hss : s ∈ Icc a b) (η : ℝ) :
      radialPartial U (s, η) = -f (s, η) * angularPartial U (s, η) := by
    have ht := canonicalGluedAiryIntegral_stored_characteristic_transport
      hS hT hN01 hN02 hN03 hA hB hz hs m (hsub ⟨hss, mem_univ _⟩)
    have he : f (s, η) = negativeCharacteristicField plus (L.coefficients z) (s, η) :=
      interiorLocalizedSpeed_eq hab.le hρ _ hss
    rw [he]
    cases plus with
    | false => simpa only [U, Bool.false_eq_true, ↓reduceIte,
        negativeCharacteristicField] using ht.1
    | true => simpa only [U, ↓reduceIte, negativeCharacteristicField] using ht.2
  exact interiorFlow_firstIntegral_eq_inverse_section hab hΘ hinverse
    (hU.continuousOn.mono hsub) hUd htransport hr θ

end ContinuousFlexibility.Analysis
