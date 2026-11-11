import ContinuousFlexibility.Radial.InnerSelectedPhysicalGeometry
import ContinuousFlexibility.Radial.ReferenceDilation

/-!
# One physical slope after independent tail dilations

The logarithmic slope is unchanged by the actual radius and height
pullback. Thus all old cap and complete-tail-gap estimates hold in the
final reference. The two fixed middle intervals supply their positive
constants by compactness. The minimum is chosen before a finite
truncation or a frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem innerSelected_Icc_subset_tail
    {D : ReferenceData} {side : Bool} {entry a b : ℝ}
    (ha : a ∈ radialTailInterval D side entry)
    (hb : b ∈ radialTailInterval D side entry) :
    Icc a b ⊆ radialTailInterval D side entry := by
  intro r hr
  cases side <;> exact ⟨ha.1.trans_le hr.1, hr.2.trans_lt hb.2⟩

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

theorem tail_profile_germ (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index)) :
    (fun x => D.w (P.radiusScale side * x)) =ᶠ[𝓝 r]
      (fun x => P.heightScale side * P.radiusScale side * (S.family S.sigma).w x) := by
  have hopen : IsOpen
      (radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index)) := by
    cases side <;> exact isOpen_Ioo
  filter_upwards [hopen.mem_nhds hr] with x hx
  exact P.profile_tail side x hx

theorem tail_derivative (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index)) :
    deriv D.w (P.radiusScale side * r) = P.heightScale side * deriv (S.family S.sigma).w r := by
  have hd := deriv_radius_pullback_of_germ (P.radiusScale_pos side).ne'
    (P.realization.geometry.2.2.1.1.differentiable (by simp) r)
    (P.geometry.2.2.1.1.differentiable (by simp) (P.radiusScale side * r))
    (P.tail_profile_germ side hr)
  simpa only [mul_div_cancel_right₀ _ (P.radiusScale_pos side).ne'] using hd

theorem tail_logSlope (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index)) :
    (P.radiusScale side * r) * deriv D.w (P.radiusScale side * r) /
        D.w (P.radiusScale side * r) =
      r * deriv (S.family S.sigma).w r / (S.family S.sigma).w r := by
  rw [P.tail_derivative side hr, P.profile_tail side r hr]
  by_cases hw : (S.family S.sigma).w r = 0
  · simp only [hw, mul_zero, div_zero]
  · field_simp [(P.radiusScale_pos side).ne', (P.heightScale_pos side).ne', hw]
    <;> ring

/-- Transport a closed-interval slope bound by the actual profile
identity, rather than replacing the final reference by a new realization. -/
theorem scaled_interval_slope (side : Bool) {a b c : ℝ}
    (htail : Icc a b ⊆
      radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index))
    (hslope : ∀ r ∈ Icc a b, c ≤ r * deriv (S.family S.sigma).w r / (S.family S.sigma).w r) :
    ∀ r ∈ Icc (P.radiusScale side * a) (P.radiusScale side * b),
      c ≤ r * deriv D.w r / D.w r := by
  intro r hr
  have hx : r / P.radiusScale side ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ (P.radiusScale_pos side)).mpr
      simpa only [mul_comm a (P.radiusScale side)] using hr.1
    · apply (div_le_iff₀ (P.radiusScale_pos side)).mpr
      simpa only [mul_comm b (P.radiusScale side)] using hr.2
  have hcancel : P.radiusScale side * (r / P.radiusScale side) = r := by
    field_simp [(P.radiusScale_pos side).ne']
  have he := P.tail_logSlope side (htail hx)
  rw [hcancel] at he
  rw [he]
  exact hslope _ hx

include P in
theorem cut_in_tail (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) (i : Fin 2) :
    innerMorseChainCut S.chain side m i ∈
      radialTailInterval (S.family S.sigma) side (S.joinInner side S.chain.index) := by
  have hd := P.realization.retained_data side m hm
  have ho := innerMorseBuffer_cut_order hd.1 hd.2.1
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · rw [innerMorseChainCut_zero]
    exact P.retained_in_tail side hm (P.buffer_subset_retained side hm
      (left_mem_Icc.mpr ho.2.1.le))
  · rw [innerMorseChainCut_one]
    exact P.retained_in_tail side hm (P.buffer_subset_retained side hm
      (right_mem_Icc.mpr ho.2.1.le))

theorem outerCap_slope (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) (right : Bool) :
    ∀ r ∈ Icc
      (P.radiusScale side * S.chain.radius side m
        (innerMorseOuterCapStart (morseChainA S.chain m) (morseChainB S.chain m) right))
      (P.radiusScale side * S.chain.radius side m
        (innerMorseOuterCapEnd (morseChainA S.chain m) (morseChainB S.chain m) right)),
      innerMorseTailSlope ≤ r * deriv D.w r / D.w r := by
  have hd := P.realization.retained_data side m hm
  obtain ⟨hl, hh⟩ := innerMorseChain_retained_endpoints P.realization side hm
  have ho := innerMorseOuterCap_order hd.1 hd.2.1 right
  have hsub : Icc
      (innerMorseOuterCapStart (morseChainA S.chain m) (morseChainB S.chain m) right)
      (innerMorseOuterCapEnd (morseChainA S.chain m) (morseChainB S.chain m) right) ⊆
      Icc (S.chain.leftX side m) (S.chain.rightX side m) := by
    intro x hx
    have hs := innerMorseOuterCap_subset hd.1 hd.2.1
      (innerMorseChain_parameter_tiny P.realization P.index_ge hm) right hx
    simpa only [hl, hh] using innerMorseCapInterval_subset hd.1 hd.2.1 right hs
  apply P.scaled_interval_slope side
    (innerSelected_Icc_subset_tail
      (P.retained_in_tail side hm (hsub (left_mem_Icc.mpr ho.le)))
      (P.retained_in_tail side hm (hsub (right_mem_Icc.mpr ho.le))))
  intro r hr
  exact innerMorseChain_outerCap_logSlope P.realization side P.index_ge hm right hr

theorem tailGap_slope (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) :
    ∀ r ∈ Icc
      (P.radiusScale side * innerMorseTailGapLeft S.chain side m)
      (P.radiusScale side * innerMorseTailGapRight S.chain side m),
      innerMorseTailSlope ≤ r * deriv D.w r / D.w r := by
  have hd : S.chain.index ≤ innerMorseTailDeparture side m := by
    cases side <;> simp only [innerMorseTailDeparture, Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  have ha : S.chain.index ≤ innerMorseTailArrival side m := by
    cases side <;> simp only [innerMorseTailArrival, Bool.false_eq_true, ite_false, ite_true] <;>
      omega
  exact P.scaled_interval_slope side
    (innerSelected_Icc_subset_tail (P.cut_in_tail side hd 1) (P.cut_in_tail side ha 0))
    (innerMorseTailGap_logSlope P.realization side P.index_ge hm)

theorem middle_exists_slope (side : Bool) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Icc (P.middleLeft side) (P.middleRight side),
      c ≤ r * deriv D.w r / D.w r := by
  have ha : 0 < P.middleLeft side :=
    P.geometry.1.trans (P.middle_core side (left_mem_Icc.mpr (P.middle_order side).le)).1
  exact innerPositiveGap_exists_slope ha P.geometry.2.2.1.1
    (fun r hr => P.geometry.2.2.2.2.1 r (P.middle_core side hr))
    (P.middle_deriv_pos side)

def middleSlope (side : Bool) : ℝ := Classical.choose (P.middle_exists_slope side)

theorem middleSlope_pos (side : Bool) : 0 < P.middleSlope side :=
  (Classical.choose_spec (P.middle_exists_slope side)).1

theorem middleSlope_lower (side : Bool) :
    ∀ r ∈ Icc (P.middleLeft side) (P.middleRight side),
      P.middleSlope side ≤ r * deriv D.w r / D.w r :=
  (Classical.choose_spec (P.middle_exists_slope side)).2

/-- This one constant depends only on the fixed physical geometry. -/
def gapSlope : ℝ := min innerMorseTailSlope (min (P.middleSlope false) (P.middleSlope true))

theorem gapSlope_pos : 0 < P.gapSlope :=
  lt_min innerMorseTailSlope_pos (lt_min (P.middleSlope_pos false) (P.middleSlope_pos true))

theorem gapSlope_le_tail : P.gapSlope ≤ innerMorseTailSlope := min_le_left _ _

theorem gapSlope_le_middle (side : Bool) : P.gapSlope ≤ P.middleSlope side := by
  cases side with
  | false => exact (min_le_right _ _).trans (min_le_left _ _)
  | true => exact (min_le_right _ _).trans (min_le_right _ _)

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
