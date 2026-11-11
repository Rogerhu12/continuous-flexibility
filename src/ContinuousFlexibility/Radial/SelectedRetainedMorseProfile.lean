import ContinuousFlexibility.Radial.SelectedSideTransport
import ContinuousFlexibility.Radial.R07MiddlePreservation

/-!
# Every original Morse cell on the same retained reference

The original selected realization supplies the cell coordinates. The
first selected matching order places every later cell outside the old
first cut. The retained pair then supplies its actual profile germ,
with the radius and height factors belonging to that side of the pair.
No realization of the entire new reference by the old chain is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The entire closed cell lies in the old core and on the retained
side of the original first cut. The entry identification follows from
the actual selected matching data. -/
theorem selected_morseCell_retained {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) {x : ℝ}
    (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    S.chain.radius side m x ∈ radialCore (S.family S.sigma) ∧
      (if side then S.cut side S.chain.index ≤ S.chain.radius side m x
       else S.chain.radius side m x ≤ S.cut side S.chain.index) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hmatch := hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband
  rcases hmatch with ⟨_, _, _, _, horder, hentry, _, _, _, _, _, _, _⟩
  have hfirst : if side then S.cut side S.chain.index < r07CellEntry S.chain side S.chain.index
      else r07CellEntry S.chain side S.chain.index < S.cut side S.chain.index := by
    cases side <;> simpa only [hentry] using horder.1.trans horder.2
  have hout := r07CellEntry_outside_middle G side hm
  have hspan := (hreal.2.2.1 side m hm).2.1.le
  have hmono := (hreal.radius_strictMonoOn side m hm).monotoneOn
  refine ⟨hreal.radius_mem_core side m hm x hx, ?_⟩
  cases side
  · have he : S.chain.radius false m (S.chain.rightX false m) ≤
        S.chain.radius false S.chain.index (S.chain.rightX false S.chain.index) := by
      simpa only [r07CellEntry, morseChainCellRightRadius, Nat.add_zero,
        Bool.false_eq_true, ite_false] using hout
    exact (hmono hx (right_mem_Icc.mpr hspan) hx.2).trans (he.trans hfirst.le)
  · have he : S.chain.radius true S.chain.index (S.chain.leftX true S.chain.index) ≤
        S.chain.radius true m (S.chain.leftX true m) := by
      simpa only [r07CellEntry, morseChainCellLeftRadius, Nat.add_zero, ite_true] using hout
    exact hfirst.le.trans (he.trans (hmono (left_mem_Icc.mpr hspan) hx hx.1))

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)

include hw hS G hband

/-- The actual common profile has the complete old-profile germ at
every point of every retained closed Morse cell, including its ends. -/
theorem reference_morse_cell_germ (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    D.w =ᶠ[𝓝 (P.sideRadius side * S.chain.radius side m x)]
      radialRadiusScale (P.sideRadius side) (P.sideHeight side * P.sideRadius side)
        (S.family S.sigma).w := by
  have hr := selected_morseCell_retained hS G hband side hm hx
  exact P.reference_side_old_germ hw hS side hr.1 hr.2

/-- Radius dilation contributes to the physical derivative. The
Liouville height itself is multiplied by the side height only. -/
theorem reference_morse_cell_profile (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m)
    {x : ℝ} (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    D.w (P.sideRadius side * S.chain.radius side m x) =
      (P.sideHeight side * morseChainAmplitude S.chain S.sigma m) *
        (P.sideRadius side * deriv (S.chain.radius side m) x) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hr := selected_morseCell_retained hS G hband side hm hx
  rw [P.reference_side_old_value hw hS side hr.1 hr.2,
    hreal.profile_eq side m hm x hx]
  ring

/-- Positivity of the actual retained profile locates the transported
cell point in the new core, without a global new-chain realization. -/
theorem reference_morse_cell_mem_core (hD : RadialProfileGeometry D)
    (side : Bool) {m : ℕ} (hm : S.chain.index ≤ m) {x : ℝ}
    (hx : x ∈ Icc (S.chain.leftX side m) (S.chain.rightX side m)) :
    P.sideRadius side * S.chain.radius side m x ∈ radialCore D := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hr := selected_morseCell_retained hS G hband side hm hx
  apply radialCore_mem_of_profile_pos hD
  rw [P.reference_side_old_value hw hS side hr.1 hr.2]
  exact mul_pos (mul_pos (P.sideHeight_pos side) (P.sideRadius_pos side))
    (hreal.geometry.2.2.2.2.1 _ hr.1)

/-- The same profile identity in the original normalized model. This
is the physical coefficient identity used by both terminal caps. -/
theorem reference_normalized_morse_profile (side : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc morseCellLeftCut
      (morseRightCapEnd (morseChainA S.chain (S.chain.index + k))
        (morseChainB S.chain (S.chain.index + k)) (1 / 100))) :
    D.w ((P.sideRadius side * G.factor side k) * G.normal k x) =
      (P.sideHeight side * morseChainAmplitude S.chain S.sigma (S.chain.index + k)) *
        ((P.sideRadius side * G.factor side k) * deriv (G.normal k) x) := by
  have hx' : x ∈ Icc (S.chain.leftX side (S.chain.index + k))
      (S.chain.rightX side (S.chain.index + k)) := by
    rw [G.leftX_eq side k, G.rightX_eq side k]
    exact hx
  have h := P.reference_morse_cell_profile hw hS G hband side (Nat.le_add_right _ _) hx'
  rw [G.radius_eq side k, deriv_const_mul_field] at h
  simpa only [mul_assoc] using h

/-- The normalized identity with the original cell index m and its
canonical normalized coordinate index m-index. -/
theorem reference_normalized_morse_profile_at (side : Bool) {m : ℕ}
    (hm : S.chain.index ≤ m) {x : ℝ}
    (hx : x ∈ Icc morseCellLeftCut
      (morseRightCapEnd (morseChainA S.chain m) (morseChainB S.chain m) (1 / 100))) :
    D.w ((P.sideRadius side * G.factor side (m - S.chain.index)) *
      G.normal (m - S.chain.index) x) =
      (P.sideHeight side * morseChainAmplitude S.chain S.sigma m) *
        ((P.sideRadius side * G.factor side (m - S.chain.index)) *
          deriv (G.normal (m - S.chain.index)) x) := by
  have he : S.chain.index + (m - S.chain.index) = m := Nat.add_sub_of_le hm
  simpa only [he] using P.reference_normalized_morse_profile hw hS G hband side
    (m - S.chain.index) (by simpa only [he] using hx)

end SeedRetainedPair

end ContinuousFlexibility.Radial
