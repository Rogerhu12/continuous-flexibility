import ContinuousFlexibility.Radial.R07DeepTailData

/-!
# Physical cell labels for the actual outward tail

Every point between two physical cuts in a chain block has that block's
partition label. On the right the outward nodes are exactly the seams.
On the left a node is the turning point inside a cell, so each edge is
split at the following seam. The same interval-to-block lemma handles
the whole right edge, both left subintervals, and the initial left glue.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

private theorem r07_three_cuts_mem_block {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) :
    T.radius right n (T.leftX right n) ∈ morseChainBlock T right n ∧
      morseChainMassEnd T right n ∈ morseChainBlock T right n ∧
      T.radius right n (T.rightX right n) ∈ morseChainBlock T right n := by
  have hc := r07_chain_model_cuts h right hn
  have hj := r07_chain_join_order h right hn
  cases right
  · have ho : T.radius false (n + 1) (T.rightX false (n + 1)) ≤
        T.radius false n (T.rightX false n) := (hj.trans (hc.1.trans hc.2)).le
    simp only [morseChainBlock, morseChainSeam, Bool.false_eq_true, if_false, uIcc_of_ge ho]
    exact ⟨⟨hj.le, (hc.1.trans hc.2).le⟩,
      ⟨(hj.trans hc.1).le, hc.2.le⟩, ⟨ho, le_rfl⟩⟩
  · have ho : T.radius true n (T.leftX true n) ≤
        T.radius true (n + 1) (T.leftX true (n + 1)) := ((hc.1.trans hc.2).trans hj).le
    simp only [morseChainBlock, morseChainSeam, if_true, uIcc_of_le ho]
    exact ⟨⟨le_rfl, ho⟩,
      ⟨hc.1.le, (hc.2.trans hj).le⟩, ⟨(hc.1.trans hc.2).le, hj.le⟩⟩

private theorem r07_label_log_interval {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) {n : ℕ} (hn : T.index ≤ n) {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haBlock : a ∈ morseChainBlock T right n) (hbBlock : b ∈ morseChainBlock T right n)
    (hx : x ∈ uIcc (r07OutwardLog right a) (r07OutwardLog right b)) :
    TailPhysicalCellAt D right n x := by
  have hr := r07_radius_mem_log_interval ha hb hx
  have hblock : tailPhysicalRadius right x ∈ morseChainBlock T right n :=
    ordConnected_uIcc.uIcc_subset haBlock hbBlock hr
  rcases h with ⟨_, _, _, _, _, _, _, _, hcover, _⟩
  exact hcover right n hn _ hblock

/-- The exact physical localization required by `R06` for the concrete
outward data of a realized Morse chain. -/
theorem r07_deepTail_localization {T : MorseChainData} {D : ReferenceData}
    {σ C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (right : Bool) (j : ℕ) {start : ℕ} (hstart : T.index < start) (η K : ℝ) :
    TailPhysicalLocalization D (r07DeepTailData T D right j start η K) right start := by
  have ha := (r07_realization_geometry h).1
  cases right
  · simp only [TailPhysicalLocalization, Bool.false_eq_true, if_false]
    constructor
    · intro n
      let m := start + n
      let seam := T.radius false (m + 1) (T.rightX false (m + 1))
      let capStart := r07OutwardLog false seam
      have hm : T.index ≤ m := hstart.le.trans (Nat.le_add_right _ _)
      have hmnext : T.index ≤ m + 1 := hm.trans (Nat.le_succ _)
      have hc := r07_chain_mass_cuts_core h false hm
      have hcn := r07_chain_mass_cuts_core h false hmnext
      have hj := r07_chain_join_order h false hm
      have hnCuts := r07_chain_model_cuts h false hmnext
      have hseam : 0 < seam := ha.trans hcn.2.2.1
      refine ⟨capStart, ?_, ?_, ?_⟩
      · have hlt := neg_lt_neg (log_lt_log hseam hj)
        simpa only [r07DeepTailData, r07MassExitRadius, r07OutwardLog,
          Bool.false_eq_true, if_false] using hlt
      · have hlt := neg_lt_neg (log_lt_log (ha.trans hcn.2.1.1) hnCuts.2)
        simpa only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog,
          Bool.false_eq_true, if_false, Nat.add_assoc] using hlt
      · intro x hx
        have hxt : x ∈ Ioo (r07OutwardLog false (morseChainMassEnd T false m))
            (r07OutwardLog false (morseChainMassEnd T false (m + 1))) := by
          simpa only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog,
            Bool.false_eq_true, if_false, Nat.add_assoc] using hx
        by_cases hxc : x < capStart
        · rw [if_pos hxc]
          exact r07_label_log_interval h false hm (ha.trans hc.2.1.1) hseam
            (r07_three_cuts_mem_block h false hm).2.1 right_mem_uIcc
            (Icc_subset_uIcc ⟨hxt.1.le, hxc.le⟩)
        · rw [if_neg hxc]
          exact r07_label_log_interval h false hmnext hseam (ha.trans hcn.2.1.1)
            left_mem_uIcc (r07_three_cuts_mem_block h false hmnext).2.1
            (Icc_subset_uIcc ⟨le_of_not_gt hxc, hxt.2.le⟩)
    · right
      refine ⟨by omega, ?_⟩
      let m := start - 1
      have hm : T.index ≤ m := by dsimp only [m]; omega
      have hmnext : m + 1 = start := by dsimp only [m]; omega
      let seam := T.radius false start (T.rightX false start)
      let capStart := r07OutwardLog false seam
      have hc := r07_chain_mass_cuts_core h false hm
      have hcn := r07_chain_mass_cuts_core h false hstart.le
      have hj : seam < T.radius false m (T.leftX false m) := by
        simpa only [hmnext, Bool.false_eq_true, if_false] using r07_chain_join_order h false hm
      have hnCuts := r07_chain_model_cuts h false hstart.le
      have hseam : 0 < seam := ha.trans hcn.2.2.1
      have hres : morseChainResistanceEnd T false start = T.radius false m (T.leftX false m) := by
        simpa only [hmnext] using (r07_chain_resistance_ends h hm).2
      refine ⟨capStart, ?_, ?_, ?_, ?_⟩
      · have hlt := neg_lt_neg (log_lt_log hseam hj)
        simpa only [r07DeepTailData, r07OutwardLog, Bool.false_eq_true, if_false, hres] using hlt
      · have hlt := neg_lt_neg (log_lt_log (ha.trans hcn.2.1.1) hnCuts.2)
        simpa only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog,
          Bool.false_eq_true, if_false, Nat.add_zero] using hlt
      · intro x hx
        have hxt : x ∈ Ico (r07OutwardLog false (T.radius false m (T.leftX false m)))
            (r07OutwardLog false seam) := by
          simpa only [r07DeepTailData, r07OutwardLog, Bool.false_eq_true, if_false, hres] using hx
        have hsBlock : seam ∈ morseChainBlock T false m := by
          change T.radius false start (T.rightX false start) ∈ morseChainBlock T false m
          rw [← hmnext]
          exact right_mem_uIcc
        exact r07_label_log_interval h false hm (ha.trans hc.1.1) hseam
          (r07_three_cuts_mem_block h false hm).1 hsBlock
          (Icc_subset_uIcc ⟨hxt.1, hxt.2.le⟩)
      · intro x hx
        have hxt : x ∈ Ico (r07OutwardLog false seam)
            (r07OutwardLog false (morseChainMassEnd T false start)) := by
          simpa only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog,
            Bool.false_eq_true, if_false, Nat.add_zero] using hx
        exact r07_label_log_interval h false hstart.le hseam (ha.trans hcn.2.1.1)
          left_mem_uIcc (r07_three_cuts_mem_block h false hstart.le).2.1
          (Icc_subset_uIcc ⟨hxt.1, hxt.2.le⟩)
  · simp only [TailPhysicalLocalization, if_true]
    refine ⟨r07_deepTail_initial_order h true j hstart η K, ?_⟩
    intro n x hx
    let m := start + n
    have hm : T.index ≤ m := hstart.le.trans (Nat.le_add_right _ _)
    have hmnext : T.index ≤ m + 1 := hm.trans (Nat.le_succ _)
    have hc := r07_chain_mass_cuts_core h true hm
    have hcn := r07_chain_mass_cuts_core h true hmnext
    have hxt : x ∈ Ioo (r07OutwardLog true (T.radius true m (T.leftX true m)))
        (r07OutwardLog true (T.radius true (m + 1) (T.leftX true (m + 1)))) := by
      simpa only [r07DeepTailData, r07MassNodeRadius, r07OutwardLog, if_true, Nat.add_assoc] using hx
    exact r07_label_log_interval h true hm (ha.trans hc.1.1) (ha.trans hcn.1.1)
      left_mem_uIcc right_mem_uIcc (Icc_subset_uIcc ⟨hxt.1.le, hxt.2.le⟩)

end ContinuousFlexibility.Radial
