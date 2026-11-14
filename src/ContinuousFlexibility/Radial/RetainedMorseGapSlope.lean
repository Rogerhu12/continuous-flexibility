module

public import ContinuousFlexibility.Radial.SelectedRetainedMorseProfile
public import ContinuousFlexibility.Radial.InnerMorseTailGap
public import ContinuousFlexibility.Radial.InnerMorsePhysicalChart

/-!
# Actual logarithmic slopes after retaining the two tails

Full profile germs transport the derivative as well as the value.
The logarithmic slope is unchanged by each side's radius and height
factors. Closed cap and complete cap-join-cap estimates therefore apply
to the new physical profile on precisely the retained intervals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem selected_morseCut_retained {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) (i : Fin 2) :
    innerMorseChainCut S.chain side m i ∈ radialCore (S.family S.sigma) ∧
      (if side then S.cut side S.chain.index ≤ innerMorseChainCut S.chain side m i
       else innerMorseChainCut S.chain side m i ≤ S.cut side S.chain.index) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hsub := innerMorseChain_buffer_subset hreal side hm
  have hab := (innerMorseBuffer_cut_order (hreal.retained_data side m hm).1
    (hreal.retained_data side m hm).2.1).2.1.le
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · rw [innerMorseChainCut_zero]
    exact selected_morseCell_retained hS G hband side hm (hsub (left_mem_Icc.mpr hab))
  · rw [innerMorseChainCut_one]
    exact selected_morseCell_retained hS G hband side hm (hsub (right_mem_Icc.mpr hab))

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)

include hw hS

theorem reference_side_old_deriv (side : Bool) {r : ℝ}
    (hr : r ∈ radialCore (S.family S.sigma))
    (ho : if side then S.cut side S.chain.index ≤ r else r ≤ S.cut side S.chain.index) :
    deriv D.w (P.sideRadius side * r) = P.sideHeight side * deriv (S.family S.sigma).w r := by
  rw [(P.reference_side_old_germ hw hS side hr ho).deriv_eq,
    deriv_radialRadiusScale_apply_mul (P.sideRadius_pos side).ne']
  congr 1
  exact mul_div_cancel_right₀ _ (P.sideRadius_pos side).ne'

theorem reference_side_old_logSlope (side : Bool) {r : ℝ}
    (hr : r ∈ radialCore (S.family S.sigma))
    (ho : if side then S.cut side S.chain.index ≤ r else r ≤ S.cut side S.chain.index) :
    (P.sideRadius side * r) * deriv D.w (P.sideRadius side * r) /
        D.w (P.sideRadius side * r) =
      r * deriv (S.family S.sigma).w r / (S.family S.sigma).w r := by
  rw [P.reference_side_old_deriv hw hS side hr ho,
    P.reference_side_old_value hw hS side hr ho]
  have hpos := (hS.2.2.2.1 S.sigma hS.2.2.1).1.geometry.2.2.2.2.1 r hr
  field_simp [(P.sideRadius_pos side).ne', (P.sideHeight_pos side).ne', hpos.ne']
  <;> ring

include G hband in
theorem reference_morse_outerCap_logSlope (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    (right : Bool) {r : ℝ}
    (hr : r ∈ Icc
      (P.sideRadius side * S.chain.radius side m
        (innerMorseOuterCapStart (morseChainA S.chain m) (morseChainB S.chain m) right))
      (P.sideRadius side * S.chain.radius side m
        (innerMorseOuterCapEnd (morseChainA S.chain m) (morseChainB S.chain m) right))) :
    innerMorseTailSlope ≤ r * deriv D.w r / D.w r := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hindex : 10 ≤ S.chain.index := (by norm_num : 10 ≤ 100).trans G.start_large
  have hAB := hreal.retained_data side m hm
  have hab := innerMorseOuterCap_order hAB.1 hAB.2.1 right
  have hwhole : Icc
      (innerMorseOuterCapStart (morseChainA S.chain m) (morseChainB S.chain m) right)
      (innerMorseOuterCapEnd (morseChainA S.chain m) (morseChainB S.chain m) right) ⊆
      Icc (S.chain.leftX side m) (S.chain.rightX side m) := by
    obtain ⟨hl, hh⟩ := innerMorseChain_retained_endpoints hreal side hm
    rw [hl, hh]
    exact (innerMorseOuterCap_subset hAB.1 hAB.2.1
      (innerMorseChain_parameter_tiny hreal hindex hm) right).trans
        (innerMorseCapInterval_subset hAB.1 hAB.2.1 right)
  have hx : r / P.sideRadius side ∈ Icc
      (S.chain.radius side m
        (innerMorseOuterCapStart (morseChainA S.chain m) (morseChainB S.chain m) right))
      (S.chain.radius side m
        (innerMorseOuterCapEnd (morseChainA S.chain m) (morseChainB S.chain m) right)) := by
    constructor
    · exact (le_div_iff₀ (P.sideRadius_pos side)).mpr (by simpa only [mul_comm] using hr.1)
    · exact (div_le_iff₀ (P.sideRadius_pos side)).mpr (by simpa only [mul_comm] using hr.2)
  have hinv := morseCellModelCoordinate_right hab.le (hreal.radius_smooth side m hm)
    ((hreal.radius_strictMonoOn side m hm).mono hwhole) hx
  have hret := selected_morseCell_retained hS G hband side hm (hwhole hinv.1)
  rw [hinv.2] at hret
  have he : P.sideRadius side * (r / P.sideRadius side) = r := by
    field_simp [(P.sideRadius_pos side).ne'] <;> ring
  have hid := P.reference_side_old_logSlope hw hS side hret.1 hret.2
  rw [he] at hid
  rw [hid]
  exact innerMorseChain_outerCap_logSlope hreal side hindex hm right hx

include G hband in
theorem reference_morse_tailGap_logSlope (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {r : ℝ} (hr : r ∈ Icc
      (P.sideRadius side * innerMorseTailGapLeft S.chain side m)
      (P.sideRadius side * innerMorseTailGapRight S.chain side m)) :
    innerMorseTailSlope ≤ r * deriv D.w r / D.w r := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hx : r / P.sideRadius side ∈ Icc
      (innerMorseTailGapLeft S.chain side m) (innerMorseTailGapRight S.chain side m) := by
    constructor
    · exact (le_div_iff₀ (P.sideRadius_pos side)).mpr (by simpa only [mul_comm] using hr.1)
    · exact (div_le_iff₀ (P.sideRadius_pos side)).mpr (by simpa only [mul_comm] using hr.2)
  have hcore := (innerMorseTailGap_geometry hreal side hm).2.2.2 hx
  have ho : if side then S.cut side S.chain.index ≤ r / P.sideRadius side
      else r / P.sideRadius side ≤ S.cut side S.chain.index := by
    cases side with
    | false =>
      exact hx.2.trans (selected_morseCut_retained hS G hband false hm 0).2
    | true =>
      exact (selected_morseCut_retained hS G hband true hm 1).2.trans hx.1
  have he : P.sideRadius side * (r / P.sideRadius side) = r := by
    field_simp [(P.sideRadius_pos side).ne'] <;> ring
  have hid := P.reference_side_old_logSlope hw hS side hcore ho
  rw [he] at hid
  rw [hid]
  exact innerMorseTailGap_logSlope hreal side
    ((by norm_num : 10 ≤ 100).trans G.start_large) hm _ hx

end SeedRetainedPair

end ContinuousFlexibility.Radial
