module

public import ContinuousFlexibility.Radial.SelectedActualEntry
public import ContinuousFlexibility.Radial.R07MiddlePreservation

/-!
# The actual later matching interval lies in the retained tail

A preceding-cell cap begins strictly outside that cell's entrance.
The canonical chain entries move outwards. Together these facts put the
entire closed cut-to-entry interval of every later band inside the open
tail retained by R08. Its actual join is included by the selected order.
No retained-position hypothesis on these three points is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

/-- The concrete preceding cap cut lies strictly outside the initial
entrance, even when the preceding cell is the initial cell itself. -/
theorem r10a_previousCellCut_strict_retained {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {σ K : ℕ → ℝ} {D : ReferenceData}
    (hreal : MorseChainRealization T σ D K) (right : Bool)
    {m : ℕ} (hm : T.index ≤ m) :
    if right then r07CellEntry T right T.index < r07PreviousCellCut T right m
      else r07PreviousCellCut T right m < r07CellEntry T right T.index := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hn : T.index ≤ T.index + k := Nat.le_add_right _ _
  have hret := hreal.retained_data right (T.index + k) hn
  have hA : 0 < morseChainA T (T.index + k) :=
    (mul_pos (by norm_num) hret.1).trans hret.2.1
  have hc := r07CapPoint_mem_cell right hret.1 hret.2.1
    (left_mem_Icc.mpr (r07CapLength_pos right hA).le)
  rw [r07CapPoint_zero] at hc
  have hx : r07CapCut right (morseChainA T (T.index + k))
      (morseChainB T (T.index + k)) ∈
      Icc (T.leftX right (T.index + k)) (T.rightX right (T.index + k)) := by
    rw [G.leftX_eq right k, G.rightX_eq right k]
    exact hc
  have hspan := (hreal.2.2.1 right (T.index + k) hn).2.1
  have hmono := hreal.radius_strictMonoOn right (T.index + k) hn
  have hentry := r07CellEntry_outside_middle G right hn
  cases right
  · have hpoint : r07CapCut false (morseChainA T (T.index + k))
        (morseChainB T (T.index + k)) < T.rightX false (T.index + k) := by
      rw [G.rightX_eq false k]
      change morseShortLeftCapCut <
        morseRightCapEnd (morseChainA T (T.index + k)) (morseChainB T (T.index + k)) (1 / 100)
      exact ((morseShortLeftCapCut_lt_leftTurn hret.1 hret.2.1).trans
        (morseTurn_order hret.1 hret.2.1)).trans_le
        (le_add_of_nonneg_right (morseRightCapLength_pos hA
          (by norm_num : (0 : ℝ) < 1 / 100)).le)
    exact (hmono hx ⟨hspan.le, le_rfl⟩ hpoint).trans_le hentry
  · have hpoint : T.leftX true (T.index + k) <
        r07CapCut true (morseChainA T (T.index + k)) (morseChainB T (T.index + k)) := by
      rw [G.leftX_eq true k]
      exact morseCellLeftCut_lt_rightTurn hret.1 hret.2.1
    exact hentry.trans_lt (hmono ⟨le_rfl, hspan.le⟩ hx hpoint)

/-- The canonical later cut and the selected ordering put the whole
closed incoming interval in the actual initial open tail. -/
theorem selected_later_span_retained {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain) (right : Bool)
    {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut right n = r07PreviousCellCut S.chain right (n - 1)) :
    S.joinInner right n ∈ uIcc (S.cut right n) (S.entry right n) ∧
      uIcc (S.cut right n) (S.entry right n) ⊆
        radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hc := r10a_previousCellCut_strict_retained G hreal right
    (by omega : S.chain.index ≤ n - 1)
  have hc' : if right then S.entry right S.chain.index < S.cut right n
      else S.cut right n < S.entry right S.chain.index := by
    rw [hentry, hcut]
    exact hc
  have h := hS.2.2.2.2.2 right n j hj heven hband
  rcases h with ⟨_, he, _, _, horder, _, _, _, _, _, _, _, _⟩
  refine ⟨?_, ?_⟩
  · cases right
    · rw [uIcc_of_ge (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
    · rw [uIcc_of_le (horder.1.trans horder.2).le]
      exact ⟨horder.1.le, horder.2.le⟩
  · intro r hr
    cases right
    · rw [uIcc_of_ge (horder.1.trans horder.2).le] at hr
      exact ⟨he.1.trans_le hr.1, hr.2.trans_lt hc'⟩
    · rw [uIcc_of_le (horder.1.trans horder.2).le] at hr
      exact ⟨hc'.trans_le hr.1, hr.2.trans_lt he.2⟩

/-- In particular the three actual later matching points, including
joinInner (the R10a matching cut), belong to the retained open tail. -/
theorem selected_later_cut_join_entry_retained {S : SelectedTailData}
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain) (right : Bool)
    {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut right n = r07PreviousCellCut S.chain right (n - 1)) :
    S.cut right n ∈ radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index) ∧
      S.joinInner right n ∈
        radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index) ∧
      S.entry right n ∈
        radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index) := by
  obtain ⟨hp, hsub⟩ := selected_later_span_retained hS G hentry right hn hj heven hband hcut
  exact ⟨hsub left_mem_uIcc, hsub hp, hsub right_mem_uIcc⟩

end ContinuousFlexibility.Radial
