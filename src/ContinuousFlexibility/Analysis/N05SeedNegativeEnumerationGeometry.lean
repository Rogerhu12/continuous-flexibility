import ContinuousFlexibility.Analysis.N05SeedOpticalLowerComponents

/-!
# The exact retained indices of the seed's negative components

The signed physical radius orders both tails outward.  Its seam intervals
separate the actual Morse turning components and recover the retained
starting index from the existing whole-component tail containment.
-/

noncomputable section

namespace ContinuousFlexibility.Radial.SeedReferenceConstruction

open Set Real
open ContinuousFlexibility.Statements

def n05SeedOutwardRadius (side : Bool) (r : ℝ) : ℝ :=
  if side then r else -r

variable {q : ℝ} (P : SeedReferenceConstruction q)

def n05OutwardSeam (side : Bool) (n : ℕ) : ℝ :=
  n05SeedOutwardRadius side (morseChainSeam P.selected.chain side n)

theorem n05_outwardSeam_monotone (side : Bool) :
    MonotoneOn (P.n05OutwardSeam side) (Ici P.selected.chain.index) := by
  apply monotoneOn_nat_Ici_of_le_succ
  intro n hn
  cases side with
  | false =>
    have hh : morseChainSeam P.selected.chain false (n + 1) <
        morseChainSeam P.selected.chain false n :=
      (morseSecondMode_joinOrder P.realization hn false).trans
        ((morseSecondMode_modelOrder P.realization false hn).1.trans
          (morseSecondMode_modelOrder P.realization false hn).2)
    exact neg_le_neg hh.le
  | true =>
    exact ((morseSecondMode_modelOrder P.realization true hn).1.trans
      (morseSecondMode_gapOrder P.realization hn true)).le

/-- Even the closed turning interval lies strictly between successive
signed seams.  The model joins and caps are therefore not extra negative
components. -/
theorem n05_model_closed_signed_block (side : Bool) {n : ℕ}
    (hn : P.selected.chain.index ≤ n) {r : ℝ}
    (hr : r ∈ Icc (P.n05ModelLeft side n) (P.n05ModelRight side n)) :
    n05SeedOutwardRadius side r ∈
      Ioo (P.n05OutwardSeam side n) (P.n05OutwardSeam side (n + 1)) := by
  obtain ⟨hl, hab, hh⟩ := morseRealization_turns_retained P.realization side hn
  have hfull := (P.realization.2.2.1 side n hn).2.1
  have hsub := Icc_subset_Icc hl.le hh.le
  have hm := P.realization.radius_strictMonoOn side n hn
  have hleft : P.selected.chain.radius side n (P.selected.chain.leftX side n) <
      P.n05ModelLeft side n :=
    hm (left_mem_Icc.mpr hfull.le) (hsub (left_mem_Icc.mpr hab.le)) hl
  have hright : P.n05ModelRight side n <
      P.selected.chain.radius side n (P.selected.chain.rightX side n) :=
    hm (hsub (right_mem_Icc.mpr hab.le)) (right_mem_Icc.mpr hfull.le) hh
  have hlow := hleft.trans_le hr.1
  have hhigh := hr.2.trans_lt hright
  have hj := morseSecondMode_joinOrder P.realization hn side
  cases side with
  | false =>
    exact ⟨neg_lt_neg hhigh, neg_lt_neg (hj.trans hlow)⟩
  | true =>
    exact ⟨hlow, hhigh.trans hj⟩

theorem n05_tail_outward_lt (side : Bool) {r : ℝ}
    (hr : r ∈ radialTailInterval (P.selected.family P.selected.sigma) side
      (P.selected.entry side P.selected.chain.index)) :
    P.n05OutwardSeam side P.retainedIndex < n05SeedOutwardRadius side r := by
  change n05SeedOutwardRadius side
      (morseChainSeam P.selected.chain side P.retainedIndex) < _
  rw [← P.entry_seam side]
  cases side with
  | false => exact neg_lt_neg hr.2
  | true => exact hr.1

/-- Every model from the retained starting index onward survives on the
same actual tail, with its whole closed turning interval. -/
theorem n05_model_closed_subset_retained_tail (side : Bool) {n : ℕ}
    (hn : P.retainedIndex ≤ n) :
    Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
      radialTailInterval (P.selected.family P.selected.sigma) side
        (P.selected.entry side P.selected.chain.index) := by
  have hn₀ := P.retainedIndex_ge.trans hn
  have hc := P.n05_model_component side hn₀
  intro r hr
  have hs := (P.n05_outwardSeam_monotone side) P.retainedIndex_ge hn₀ hn
  have ho := hs.trans_lt (P.n05_model_closed_signed_block side hn₀ hr).1
  change n05SeedOutwardRadius side
      (morseChainSeam P.selected.chain side P.retainedIndex) < _ at ho
  rw [← P.entry_seam side] at ho
  cases side with
  | false => exact ⟨hc.1.trans_le hr.1, neg_lt_neg_iff.mp ho⟩
  | true => exact ⟨ho, hr.2.trans_lt hc.2.2.1⟩

/-- The whole-tail condition already present in the component classifier
forces its model index to be at least the actual retained index. -/
theorem n05_model_index_ge_retained (side : Bool) {n : ℕ}
    (hn : P.selected.chain.index ≤ n)
    (hclosed : Icc (P.n05ModelLeft side n) (P.n05ModelRight side n) ⊆
      radialTailInterval (P.selected.family P.selected.sigma) side
        (P.selected.entry side P.selected.chain.index)) :
    P.retainedIndex ≤ n := by
  have hp := left_mem_Icc.mpr (P.n05_model_component side hn).2.1.le
  have hb := P.n05_model_closed_signed_block side hn hp
  have ht := P.n05_tail_outward_lt side (hclosed hp)
  by_contra hh
  have hnext : n + 1 ≤ P.retainedIndex := by omega
  have hs := (P.n05_outwardSeam_monotone side)
    (hn.trans (Nat.le_succ n)) P.retainedIndex_ge hnext
  exact (lt_irrefl _) ((hb.2.trans_le hs).trans ht)

/-- Two closed Morse turning intervals on the same side cannot contain
the same physical point unless their model indices agree. -/
theorem n05_model_index_eq_of_mem (side : Bool) {n m : ℕ}
    (hn : P.selected.chain.index ≤ n) (hm : P.selected.chain.index ≤ m) {r : ℝ}
    (hrn : r ∈ Icc (P.n05ModelLeft side n) (P.n05ModelRight side n))
    (hrm : r ∈ Icc (P.n05ModelLeft side m) (P.n05ModelRight side m)) : n = m := by
  have hbn := P.n05_model_closed_signed_block side hn hrn
  have hbm := P.n05_model_closed_signed_block side hm hrm
  rcases lt_trichotomy n m with hnm | heq | hmn
  · have hs := (P.n05_outwardSeam_monotone side)
      (hn.trans (Nat.le_succ n)) hm (Nat.succ_le_of_lt hnm)
    exact False.elim ((lt_irrefl _) ((hbn.2.trans_le hs).trans hbm.1))
  · exact heq
  · have hs := (P.n05_outwardSeam_monotone side)
      (hm.trans (Nat.le_succ m)) hn (Nat.succ_le_of_lt hmn)
    exact False.elim ((lt_irrefl _) ((hbm.2.trans_le hs).trans hbn.1))

/-- Exact component classification, now retaining the actual starting
index instead of only the original chain's weaker lower bound. -/
theorem n05_component_cases_retained (hq : 0 < q) {l h : ℝ}
    (hc : NegativeRadialComponent P.reference l h) :
    (l = centralRadius (-sqrt centralOscillatorA) ∧
      h = centralRadius (sqrt centralOscillatorA)) ∨
    ∃ (side : Bool) (n : ℕ), P.retainedIndex ≤ n ∧
      l = P.n05TailScale side * P.n05ModelLeft side n ∧
      h = P.n05TailScale side * P.n05ModelRight side n := by
  rcases P.n05_component_cases hq hc with hc | ⟨side, n, hn, hl, hh, hclosed⟩
  · exact Or.inl hc
  · exact Or.inr ⟨side, n, P.n05_model_index_ge_retained side hn hclosed, hl, hh⟩

end ContinuousFlexibility.Radial.SeedReferenceConstruction
