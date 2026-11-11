import ContinuousFlexibility.Radial.RetainedMorseInnerGeometry

/-!
# Positivity on the two actual middle gaps

The middle gap is split into a retained Morse cap, the original first
cut-to-entry bridge, and the already fixed central connector. Only the
actual derivative positivity of the short bridge is used. No uniform
lower bound for that bridge is asserted or needed by the Hardy estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)

include hw hS hfirst in
theorem reference_first_bridge_deriv_pos
    (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
      (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
    (side : Bool) {r : ℝ}
    (hr : r ∈ uIcc (P.sideRadius side * S.cut side S.chain.index)
      (P.sideRadius side * S.entry side S.chain.index)) :
    0 < deriv D.w r := by
  have hκ := P.sideRadius_pos side
  have hx := (mem_uIcc_div_pos hκ).mpr hr
  have hm := hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hfirst
  have hxCore : r / P.sideRadius side ∈ radialCore (S.family S.sigma) :=
    ⟨(lt_min hm.1.1 hm.2.1.1).trans_le hx.1,
      hx.2.trans_lt (max_lt hm.1.2 hm.2.1.2)⟩
  have ho : if side then S.cut side S.chain.index ≤ r / P.sideRadius side
      else r / P.sideRadius side ≤ S.cut side S.chain.index := by
    have ho := hm.2.2.2.2.1
    cases side
    · rw [uIcc_of_ge (ho.1.trans ho.2).le] at hx
      exact hx.2
    · rw [uIcc_of_le (ho.1.trans ho.2).le] at hx
      exact hx.1
  have he : P.sideRadius side * (r / P.sideRadius side) = r := by
    field_simp [hκ.ne'] <;> ring
  have hd := P.reference_side_old_deriv hw hS side hxCore ho
  rw [he] at hd
  rw [hd]
  exact mul_pos (P.sideHeight_pos side) (hbridge side _ hx)

end SeedRetainedPair

theorem retained_deriv_pos_of_logSlope {w : ℝ → ℝ} {r c : ℝ}
    (hr : 0 < r) (hw : 0 < w r) (hc : 0 < c)
    (hs : c ≤ r * deriv w r / w r) : 0 < deriv w r := by
  have hprod := mul_pos (hc.trans_le hs) hw
  rw [div_mul_cancel₀ _ hw.ne'] at hprod
  exact (mul_pos_iff_of_pos_left hr).mp hprod

namespace SeedRetainedPair

theorem reference_morse_middle_deriv_pos {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length T : ℝ} (P : SeedRetainedPair S K q length)
    {Γ : ConnectedReferenceGeometry} (hw : Γ.reference.w = P.pair.profile)
    (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
      (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hT : 0 ≤ T) (hTL : Γ.centralLeft < centralRadius (-T))
    (hTR : centralRadius T < Γ.centralRight)
    (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
    (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
      (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
    (side : Bool) {r : ℝ} (hr : 0 < r) (hwr : 0 < Γ.reference.w r)
    (hgap : r ∈ Icc
      (scaledMorseMiddleGapLeft S.chain P.sideRadius S.chain.index (retainedMorseCenterCuts T) side)
      (scaledMorseMiddleGapRight S.chain P.sideRadius S.chain.index (retainedMorseCenterCuts T) side)) :
    0 < deriv Γ.reference.w r := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hm := hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hfirst
  have hentry := hm.2.2.2.2.2.1
  have hends := innerMorseChain_retained_endpoints hreal side (le_refl S.chain.index)
  have hcentral (hg : r ∈
      Icc (P.pair.radiusL * S.cut false S.chain.index) (centralRadius (-T)) ∪
      Icc (centralRadius T) (P.pair.radiusR * S.cut true S.chain.index)) :
      0 < deriv Γ.reference.w r := by
    have hh := P.reference_buffer_gap_logSlope hw hleft hright hT hTL hTR hmodel hwindow hr hg
    have hp : 0 < r * deriv Γ.reference.w r :=
      (mul_pos (by norm_num : (0 : ℝ) < 3 / 4) hwr).trans_le hh
    exact (mul_pos_iff_of_pos_left hr).mp hp
  cases side with
  | false =>
    change P.sideRadius false * innerMorseChainCut S.chain false S.chain.index 1 ≤ r ∧
      r ≤ centralRadius (-T) at hgap
    by_cases he : r ≤ P.sideRadius false * S.entry false S.chain.index
    · apply retained_deriv_pos_of_logSlope hr hwr innerMorseTailSlope_pos
      apply P.reference_morse_outerCap_logSlope hw hS G₀ hfirst false le_rfl true
      constructor
      · simpa only [innerMorseOuterCapStart, ite_true, innerMorseChainCut_one] using hgap.1
      · simpa only [hentry, Bool.false_eq_true, ite_false, hends.2,
          innerMorseOuterCapEnd, ite_true] using he
    by_cases hc : r ≤ P.sideRadius false * S.cut false S.chain.index
    · apply P.reference_first_bridge_deriv_pos hw hS hfirst hbridge false
      exact ⟨(min_le_right _ _).trans (lt_of_not_ge he).le,
        hc.trans (le_max_left _ _)⟩
    · exact hcentral (Or.inl ⟨(lt_of_not_ge hc).le, hgap.2⟩)
  | true =>
    change centralRadius T ≤ r ∧
      r ≤ P.sideRadius true * innerMorseChainCut S.chain true S.chain.index 0 at hgap
    by_cases he : P.sideRadius true * S.entry true S.chain.index ≤ r
    · apply retained_deriv_pos_of_logSlope hr hwr innerMorseTailSlope_pos
      apply P.reference_morse_outerCap_logSlope hw hS G₀ hfirst true le_rfl false
      constructor
      · simpa only [hentry, ite_true, hends.1, innerMorseOuterCapStart,
          Bool.false_eq_true, ite_false] using he
      · simpa only [innerMorseOuterCapEnd, Bool.false_eq_true, ite_false,
          innerMorseChainCut_zero] using hgap.2
    by_cases hc : P.sideRadius true * S.cut true S.chain.index ≤ r
    · apply P.reference_first_bridge_deriv_pos hw hS hfirst hbridge true
      exact ⟨(min_le_left _ _).trans hc,
        (lt_of_not_ge he).le.trans (le_max_right _ _)⟩
    · exact hcentral (Or.inr ⟨hgap.1, (lt_of_not_ge hc).le⟩)

end SeedRetainedPair

end ContinuousFlexibility.Radial
