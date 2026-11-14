module

public import ContinuousFlexibility.Analysis.N06MorsePositiveComponent

/-!
# Actual cell labels across a positive Morse gap

The departure cap, original join and arrival cap lie in the two actual
seam blocks numbered n and n + 1. The realization certificate supplies
an original open cell at each physical point. No single cell is asserted
to contain the entire positive component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

private theorem morseRealization_model_interval_cell
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) {r : ℝ}
    (hr : r ∈ Icc (T.radius side n (T.leftX side n))
      (T.radius side n (T.rightX side n))) :
    ∃ m, D.cellIndex m = n ∧ r ∈ D.cells m := by
  obtain ⟨x, hx, hxr⟩ := intermediate_value_Icc
    (hreal.2.2.1 side n hn).2.1.le
    (hreal.radius_smooth side n hn).continuous.continuousOn hr
  exact hreal.2.2.2.2.2.2.2.2.1 side n hn r
    (morseRealization_model_subset_block hreal side hn ⟨x, hx, hxr⟩)

private theorem morseRealization_join_subset_block
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    Icc (T.joinLeft side n) (T.joinRight side n) ⊆ morseChainBlock T side n := by
  have horder := (hreal.2.2.1 side n hn).2.1
  have hleft := morseRealization_model_subset_block hreal side hn
    ⟨T.leftX side n, left_mem_Icc.mpr horder.le, rfl⟩
  have hright := morseRealization_model_subset_block hreal side hn
    ⟨T.rightX side n, right_mem_Icc.mpr horder.le, rfl⟩
  have hj := hreal.join_data side n hn
  have hjL : T.joinLeft side n ∈ morseChainBlock T side n := by
    rw [hj.2.1]
    cases side
    · change T.radius false (n + 1) (T.rightX false (n + 1)) ∈
        uIcc (T.radius false n (T.rightX false n))
          (T.radius false (n + 1) (T.rightX false (n + 1)))
      exact right_mem_uIcc
    · exact hright
  have hjR : T.joinRight side n ∈ morseChainBlock T side n := by
    rw [hj.2.2.1]
    cases side
    · exact hleft
    · change T.radius true (n + 1) (T.leftX true (n + 1)) ∈
        uIcc (T.radius true n (T.leftX true n))
          (T.radius true (n + 1) (T.leftX true (n + 1)))
      exact right_mem_uIcc
  exact Icc_subset_uIcc.trans (uIcc_subset_uIcc hjL hjR)

/-- Every point of the closed positive gap belongs to an actual original
cell of index n or n + 1. This includes both turning roots. -/
theorem morseRealization_positive_gap_cell_labels
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) {r : ℝ}
    (hr : r ∈ Icc (n06MorsePositiveLeft T side n) (n06MorsePositiveRight T side n)) :
    ∃ m, (D.cellIndex m = n ∨ D.cellIndex m = n + 1) ∧ r ∈ D.cells m := by
  let d : ℕ := if side then n else n + 1
  let a : ℕ := if side then n + 1 else n
  have hd : T.index ≤ d := by
    cases side
    · exact hn.trans (Nat.le_succ n)
    · exact hn
  have ha : T.index ≤ a := by
    cases side
    · exact hn
    · exact hn.trans (Nat.le_succ n)
  have hdlabel : d = n ∨ d = n + 1 := by
    cases side
    · exact Or.inr rfl
    · exact Or.inl rfl
  have halabel : a = n ∨ a = n + 1 := by
    cases side
    · exact Or.inl rfl
    · exact Or.inr rfl
  have finish (k : ℕ) (hk : k = n ∨ k = n + 1)
      (hc : ∃ m, D.cellIndex m = k ∧ r ∈ D.cells m) :
      ∃ m, (D.cellIndex m = n ∨ D.cellIndex m = n + 1) ∧ r ∈ D.cells m := by
    obtain ⟨m, hm, hrm⟩ := hc
    exact ⟨m, hk.imp (fun h => hm.trans h) (fun h => hm.trans h), hrm⟩
  have hj := hreal.join_data side n hn
  have hjL : T.joinLeft side n = T.radius side d (T.rightX side d) := by
    cases side <;> exact hj.2.1
  have hjR : T.joinRight side n = T.radius side a (T.leftX side a) := by
    cases side <;> exact hj.2.2.1
  by_cases hleft : r ≤ T.joinLeft side n
  · obtain ⟨hl, hlr, hh⟩ := morseRealization_turns_retained hreal side hd
    have hfull := (hreal.2.2.1 side d hd).2.1
    have hlow : T.radius side d (T.leftX side d) ≤ n06MorsePositiveLeft T side n :=
      (hreal.radius_strictMonoOn side d hd).monotoneOn
        (left_mem_Icc.mpr hfull.le) ⟨(hl.trans hlr).le, hh.le⟩ (hl.trans hlr).le
    apply finish d hdlabel
    apply morseRealization_model_interval_cell hreal side hd
    exact ⟨hlow.trans hr.1, hleft.trans_eq hjL⟩
  · by_cases hright : T.joinRight side n ≤ r
    · obtain ⟨hl, hlr, hh⟩ := morseRealization_turns_retained hreal side ha
      have hfull := (hreal.2.2.1 side a ha).2.1
      have hhigh : n06MorsePositiveRight T side n ≤ T.radius side a (T.rightX side a) :=
        (hreal.radius_strictMonoOn side a ha).monotoneOn
          ⟨hl.le, (hlr.trans hh).le⟩ (right_mem_Icc.mpr hfull.le) (hlr.trans hh).le
      apply finish a halabel
      apply morseRealization_model_interval_cell hreal side ha
      exact ⟨hjR ▸ hright, hr.2.trans hhigh⟩
    · apply finish n (Or.inl rfl)
      exact hreal.2.2.2.2.2.2.2.2.1 side n hn r
        (morseRealization_join_subset_block hreal side hn
          ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩)

end ContinuousFlexibility.Analysis
