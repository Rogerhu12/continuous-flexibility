module

public import ContinuousFlexibility.Analysis.InteriorTravelSectionBounds
public import ContinuousFlexibility.Analysis.CanonicalInteriorAngularClosure
public import ContinuousFlexibility.Analysis.CanonicalRootTravelDomain
public import ContinuousFlexibility.Analysis.N03InteriorFirstIntegralIdentification

/-!
# Two true root-section bounds control travel throughout the interior

The actual first integrals solve the stored characteristic equations.
The smooth localized plus flow preserves these equations on the tested
strip. Its real trajectories propagate the left lower bound and the
right upper bound. Both root orientations consequently share one
positive travel interval, with no fixed-angle radial monotonicity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n03_interiorRootTravel_bounds_of_actual_sections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {a b ρ l u ℓL ℓR : ℝ} (ha : C.left m < a) (hab : a < b) (hb : b < C.right m)
    (hρ : 0 < ρ) (hmarginL : C.left m < a - 2 * ρ)
    (hmarginR : b + 2 * ρ < C.right m)
    (hl : 0 ≤ l) (hℓL : 0 ≤ ℓL) (hℓR : 0 ≤ ℓR)
    (hangular : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      angularPartial (canonicalGluedAiryIntegral S K z m 1) (r, θ) ∈ Icc l u)
    (hleft : ∀ θ : ℝ, ℓL ≤ canonicalGluedRootTravel S K z m false (a, θ))
    (hright : ∀ θ : ℝ, ℓR ≤ canonicalGluedRootTravel S K z m true (b, θ))
    {Θ Ψ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (interiorScalarFlowField
        (interiorLocalizedSpeed hab.le hρ (negativeCharacteristicField true (L.coefficients z)))
          a b) Θ)
    (hinverse : ∀ v θ, Θ v 1 (Ψ v 1 θ) = θ)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) (side : Bool) :
    canonicalGluedRootTravel S K z m side (r, θ) ∈
      Icc (min ℓL ℓR) (2 * airyTravelPrimitive (K.cutRadius m)) := by
  let U := canonicalGluedAiryIntegral S K z m 1
  let V := canonicalGluedAiryIntegral S K z m (-1)
  let fm := interiorLocalizedSpeed hab.le hρ
    (negativeCharacteristicField false (L.coefficients z))
  let fp := interiorLocalizedSpeed hab.le hρ
    (negativeCharacteristicField true (L.coefficients z))
  have hsub : Icc a b ×ˢ (univ : Set ℝ) ⊆
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    fun q hq => ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt hb⟩, mem_univ _⟩
  have hdiff (σ s : ℝ) (hss : s ∈ Icc a b) (φ : ℝ) :
      DifferentiableAt ℝ (canonicalGluedAiryIntegral S K z m σ) (s, φ) :=
    (((contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ) _
      (hsub ⟨hss, mem_univ _⟩)).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hsub ⟨hss, mem_univ _⟩))).differentiableAt_one
  have hUc : ContinuousOn U (Icc a b ×ˢ (univ : Set ℝ)) :=
    (contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m 1).continuousOn.mono hsub
  have hVc : ContinuousOn V (Icc a b ×ˢ (univ : Set ℝ)) :=
    (contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m (-1)).continuousOn.mono hsub
  have hlocal (plus : Bool) (s : ℝ) (hss : s ∈ Icc a b) (φ : ℝ) :
      interiorLocalizedSpeed hab.le hρ (negativeCharacteristicField plus (L.coefficients z))
        (s, φ) = negativeCharacteristicField plus (L.coefficients z) (s, φ) :=
    interiorLocalizedSpeed_eq hab.le hρ _ hss
  have htransport (s : ℝ) (hss : s ∈ Icc a b) (φ : ℝ) :
      radialPartial U (s, φ) = -fm (s, φ) * angularPartial U (s, φ) ∧
        radialPartial V (s, φ) = -fp (s, φ) * angularPartial V (s, φ) := by
    have h := canonicalGluedAiryIntegral_stored_characteristic_transport
      hS hT hN01 hN02 hN03 hA hB hz hs m (p := (s, φ)) (hsub ⟨hss, mem_univ _⟩)
    dsimp only [U, V, fm, fp]
    rw [hlocal false s hss φ, hlocal true s hss φ]
    simpa only [negativeCharacteristicField, Bool.false_eq_true, ↓reduceIte] using h
  have hordered (s : ℝ) (hss : s ∈ Icc a b) (φ : ℝ) : fm (s, φ) ≤ fp (s, φ) := by
    have hqN := hsub (show (s, φ) ∈ Icc a b ×ˢ (univ : Set ℝ) from ⟨hss, mem_univ _⟩)
    have hends := hN01.2.2.2.1.1 m
    have hqAnn : (s, φ) ∈ annularOpen D :=
      ⟨⟨hends.1.trans hqN.1.1, hqN.1.2.trans hends.2.2⟩, mem_univ _⟩
    have hapos : 0 < (L.coefficients z).a (s, φ) := by
      rw [hN03.1 z hz hs (s, φ)]
      exact n01_originalRadialCoefficient_pos hN01 hz hs hqAnn
    have hv : 0 ≤ Real.sqrt ((L.coefficients z).b (s, φ) ^ 2 -
        (L.coefficients z).a (s, φ) * (L.coefficients z).c (s, φ)) /
          (L.coefficients z).a (s, φ) := div_nonneg (Real.sqrt_nonneg _) hapos.le
    dsimp only [fm, fp]
    rw [hlocal false s hss φ, hlocal true s hss φ]
    simp only [negativeCharacteristicField, minusCharacteristicSpeed,
      plusCharacteristicSpeed, Bool.false_eq_true, ↓reduceIte]
    linarith only [hv]
  have hnonnegative (s : ℝ) (hss : s ∈ Icc a b) (φ : ℝ) : 0 ≤ angularPartial U (s, φ) :=
    hl.trans (canonicalGluedAiryIntegral_angular_bounds_closedStrip
      hA hB hz hs m 1 ha hab hb hangular hss φ).1
  have h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε :=
    ⟨⟨hN01, hN02⟩, hN03⟩
  have houter : Ioo (a - 2 * ρ) (b + 2 * ρ) ⊆ Ioo (C.left m) (C.right m) :=
    fun s hss => ⟨hmarginL.trans hss.1, hss.2.trans hmarginR⟩
  have hfp : ContDiff ℝ ∞ fp := by
    apply contDiff_interiorLocalizedSpeed
    intro q hq
    exact (n04b_corrected_characteristics_contDiffAt h03 hfield hz hs m
      ⟨houter hq.1, mem_univ _⟩).2.2.2.contDiffWithinAt
  have hperiod : ∀ s : ℝ, Function.Periodic (fun φ => fp (s, φ)) Real.pi := by
    apply interiorLocalizedSpeed_periodic
    intro s hss
    have hends := hN01.2.2.2.1.1 m
    have hn := houter hss
    have hc := hfield.periodic_coefficients z hz hs s
      ⟨hends.1.trans hn.1, hn.2.trans hends.2.2⟩
    have hdv := n04b_characteristic_periodic (L.coefficients z) s Real.pi hc.1 hc.2.1 hc.2.2
    exact hdv.1.add hdv.2
  have hlow : ℓL ≤ (U (r, θ) - V (r, θ)) / 2 :=
    interiorTravel_lowerBound_of_leftSection hUc hVc
      (hdiff 1) (hdiff (-1)) (fun s hss φ => (htransport s hss φ).1)
      (fun s hss φ => (htransport s hss φ).2) hordered hnonnegative
      hab hΘ hinverse hleft hr θ
  have hhigh : (U (r, θ) - V (r, θ)) / 2 ≤
      2 * airyTravelPrimitive (K.cutRadius m) - ℓR := by
    apply interiorTravel_upperBound_of_rightSection hUc hVc
      (hdiff 1) (hdiff (-1)) (fun s hss φ => (htransport s hss φ).1)
      (fun s hss φ => (htransport s hss φ).2) hordered hnonnegative hfp hperiod ?_ hr θ
    intro φ
    have h := hright φ
    change ℓR ≤ 2 * airyTravelPrimitive (K.cutRadius m) - (U (b, φ) - V (b, φ)) / 2 at h
    linarith only [h]
  have hmL : min ℓL ℓR ≤ ℓL := min_le_left _ _
  have hmR : min ℓL ℓR ≤ ℓR := min_le_right _ _
  change (if side then 2 * airyTravelPrimitive (K.cutRadius m) -
    (U (r, θ) - V (r, θ)) / 2 else (U (r, θ) - V (r, θ)) / 2) ∈ _
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨hmL.trans hlow, by linarith only [hhigh, hℓR]⟩
  · exact ⟨by linarith only [hhigh, hmR], by linarith only [hlow, hℓL]⟩

end ContinuousFlexibility.Analysis
