import ContinuousFlexibility.Analysis.N03InteriorFirstIntegralJets
import ContinuousFlexibility.Analysis.InteriorLabelAngularBounds
import ContinuousFlexibility.Analysis.RootScaledAngularBounds

/-!
# Actual first-integral angular bounds throughout a negative interior

The original N01 left label and the same controlled root flow give a
uniformly positive section derivative. The actual interior inverse
flow propagates this bound to the original glued first integrals. The
constants depend only on the two actual angular-control exponents.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_interiorFirstIntegral_angular_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss rootLoss flowLoss : ℕ}
    {ε : ℝ} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hE : N02Properties D T S C E base ε)
    (hL : N03Properties D T S C E L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R κ δ Λ η x b ρ Γ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : η ≤ 1)
    (hx : x ∈ Ioc (0 : ℝ) η) (hab : C.left m + δ * x < b)
    (hb : b < C.right m) (hρ : 0 < ρ)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (C.left m) 1 R)
    {A F : ℕ → ℝ}
    (hinput : N01ControlledRootInputAtState D S C m false g hR κ δ Λ rootLoss A z)
    (hfixed : N03FixedRootFlowIdentification D S C L base ε m false g hR δ η)
    (hflows : ∀ plus : Bool, ∃ Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      InteriorFlowPairBounds (pairGrading (stateGrading S) realGrading) flowLoss F
        (z - (C.referenceState, 0)) Γ (C.left m + δ * x) b
        (interiorLocalizedSpeed hab.le hρ
          (negativeCharacteristicField plus (L.coefficients z))) Θ Ψ) :
    ∀ plus : Bool, ∀ q : PolarPoint, q.1 ∈ Ioo (C.left m + δ * x) b →
      angularPartial (canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) q ∈
        Icc ((Real.exp (-Λ) / 4) * Real.exp (-Γ)) ((4 * Real.exp Λ) * Real.exp Γ) := by
  let a := C.left m + δ * x
  have ha : C.left m < a := lt_add_of_pos_right _ (mul_pos hδ hx.1)
  have hax : a ∈ Ioo (C.left m) (C.right m) := ⟨ha, hab.trans hb⟩
  have hxone : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hη⟩
  obtain ⟨hcontrol, Θ₀, hΘ₀, hG, _hperiod, _hzero, _hlower, _hrootjets⟩ := hinput
  let G := rootScaledInverseCoordinate Θ₀ (n01RootLabel S C z m false) (Real.sqrt δ)
  have hmatch := hfixed z hz hs Θ₀ hΘ₀
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g (C.left m) 1 hR z
  have hlabel := n01RootLabel_contDiff hS hT hN hz hs m false
  have hlabelBounds (θ : ℝ) : deriv (n01RootLabel S C z m false) θ ∈ Icc (1 / 4 : ℝ) 4 := by
    have hh := hN.2.2.2.2.2.2.2.1 z hz hs m θ
    exact ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans hh.1,
      hh.2.1.trans (by norm_num : (2 : ℝ) ≤ 4)⟩
  have hτ : |Real.sqrt δ| ≤ 1 := by
    simpa only [one_mul] using
      abs_signed_sqrt_le_one (η := (1 : ℝ)) hδ.le hδone (Or.inl rfl)
  intro plus q hq
  obtain ⟨Θ, Ψ, hΘ, _hΨeq, hinverse, _hΘjets, hΨjets⟩ := hflows plus
  let ζ : ℝ := (if plus then 1 else -1) * x ^ (3 / 2 : ℝ)
  let u : ℝ → ℝ := rootCircleSample G x ζ
  let U := canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)
  have hpow : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx.1.le _
  have hpowone : x ^ (3 / 2 : ℝ) ≤ 1 :=
    (Real.rpow_le_self_of_le_one hxone.1 hxone.2 (by norm_num)).trans hxone.2
  have hζ : ζ ∈ Icc (-1 : ℝ) 1 := by
    cases plus <;> simp only [ζ, Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul]
    · exact ⟨neg_le_neg hpowone, (neg_nonpos.mpr hpow).trans zero_le_one⟩
    · exact ⟨(by linarith only [hpow]), hpowone⟩
  have hub (θ : ℝ) : deriv u θ ∈ Icc (Real.exp (-Λ) / 4) (4 * Real.exp Λ) :=
    rootScaledInverseCoordinate_angular_deriv_bounds hregular.1 hregular.2
      hperiod.1 hperiod.2 hΘ₀ hcontrol hlabel hlabelBounds hτ
      ⟨(by linarith only [hxone.1]), hxone.2⟩ hζ θ
  have he : EqOn U (fun y => u (interiorEndpointPullback Ψ a b y))
      (Ioo a b ×ˢ (univ : Set ℝ)) := by
    intro y hy
    have htransport := canonicalGluedAiryIntegral_eq_interiorFlowInverse
      hS hT hN hE hL hA hB hz hs m ha hab hb hρ plus hΘ
      (fun v θ => (hinverse v θ).1) (Ioo_subset_Icc_self hy.1) y.2
    have hsection := n03_leftRoot_firstIntegrals_eq_controlled_samples
      hS hT hN hE hL hA hB hz hs m hg hR hstrip hΘ₀ hmatch hx hax
      (interiorEndpointPullback Ψ a b y)
    cases plus with
    | false => exact htransport.trans (by
        simpa only [u, G, ζ, Bool.false_eq_true, ↓reduceIte, neg_one_mul] using hsection.1)
    | true => exact htransport.trans (by
        simpa only [u, G, ζ, ↓reduceIte, one_mul] using hsection.2)
  exact interiorTransportedLabel_angular_bounds hab
    (div_nonneg (Real.exp_pos _).le (by norm_num)) (contDiff_rootCircleSample hG x ζ) hub
    (hΨjets 1 ⟨zero_le_one, le_rfl⟩).1 (hΨjets 1 ⟨zero_le_one, le_rfl⟩).2.2.1
    (isOpen_Ioo.prod isOpen_univ) (fun y hy => Ioo_subset_Icc_self hy.1) he
    ⟨hq, mem_univ _⟩

end ContinuousFlexibility.Analysis
