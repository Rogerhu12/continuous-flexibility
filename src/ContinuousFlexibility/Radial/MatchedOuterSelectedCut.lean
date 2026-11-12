import ContinuousFlexibility.Radial.OuterTransitionCoordinates
import ContinuousFlexibility.Radial.R07ChainIncoming

/-!
# The selected matching join is the actual outer-core endpoint

For every later band the selected join is the outward endpoint of the
preceding retained cell.  The existing glue endpoint identity identifies
it exactly with the endpoint used by the quantitative whole Green
estimate.  No transfer through the preceding long cap is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements

theorem matchedMorse_transitionEntry_eq_previousJoin
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (entry : ℝ) (right : Bool)
    {n : ℕ} (hn : T.index < n) :
    morseTransitionPhysicalEntry T entry right n =
      r07PreviousCellJoin T right (n - 1) := by
  have hn₀ : T.index ≤ n - 1 := by omega
  have hne : n ≠ T.index := Nat.ne_of_gt hn
  have hj := h.join_data right (n - 1) hn₀
  cases right with
  | false =>
      simpa only [morseTransitionPhysicalEntry, morseTransitionCoreRight,
        if_neg hne, morseOuterFullCoreRight, morseOuterCoreRight,
        r07PreviousCellJoin, Bool.false_eq_true, if_false] using hj.2.2.1
  | true =>
      simpa only [morseTransitionPhysicalEntry, morseTransitionCoreLeft,
        if_neg hne, morseOuterCoreLeft, r07PreviousCellJoin, if_true] using hj.2.1

theorem matchedMorse_transitionOutwardLeft_eq_selectedJoin
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (entry : ℝ) (right : Bool)
    {n : ℕ} (hn : T.index < n) {join : ℝ}
    (hjoin : join = r07PreviousCellJoin T right (n - 1)) :
    morseTransitionOutwardLeft T entry right n =
      outerOutwardRadius right join := by
  rw [morseTransitionOutwardLeft_eq,
    matchedMorse_transitionEntry_eq_previousJoin h entry right hn, ← hjoin]

/-- The preceding selected join has the original preceding-cell label. -/
theorem matchedMorse_previousJoin_mem_block
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool)
    (m : ℕ) (hm : T.index ≤ m) :
    r07PreviousCellJoin T right m ∈ morseChainBlock T right m := by
  have hr := morseRealized_retained_endpoints h right m hm
  have hj := h.join_data right m hm
  cases right with
  | false =>
      change min (T.radius false m (T.rightX false m))
          (T.radius false (m + 1) (T.rightX false (m + 1))) ≤
          T.radius false m (T.leftX false m) ∧
        T.radius false m (T.leftX false m) ≤
          max (T.radius false m (T.rightX false m))
            (T.radius false (m + 1) (T.rightX false (m + 1)))
      have hgap : T.radius false (m + 1) (T.rightX false (m + 1)) <
          T.radius false m (T.leftX false m) := by
        simpa only [hj.2.1, hj.2.2.1, Bool.false_eq_true, if_false] using hj.1
      exact ⟨(min_le_right _ _).trans hgap.le, hr.2.2.le.trans (le_max_left _ _)⟩
  | true =>
      change min (T.radius true m (T.leftX true m))
          (T.radius true (m + 1) (T.leftX true (m + 1))) ≤
          T.radius true m (T.rightX true m) ∧
        T.radius true m (T.rightX true m) ≤
          max (T.radius true m (T.leftX true m))
            (T.radius true (m + 1) (T.leftX true (m + 1)))
      have hgap : T.radius true m (T.rightX true m) <
          T.radius true (m + 1) (T.leftX true (m + 1)) := by
        simpa only [hj.2.1, hj.2.2.1, if_true] using hj.1
      exact ⟨(min_le_left _ _).trans hr.2.2.le, hgap.le.trans (le_max_right _ _)⟩

theorem matchedMorse_previousJoin_cell
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (h : MorseChainRealization T σ D C) (right : Bool)
    (m : ℕ) (hm : T.index ≤ m) :
    ∃ k : ℕ, D.cellIndex k = m ∧ r07PreviousCellJoin T right m ∈ D.cells k := by
  have hblock := matchedMorse_previousJoin_mem_block h right m hm
  rcases h with ⟨_, _, _, _, _, _, _, _, hcover, _⟩
  exact hcover right m hm _ hblock

end ContinuousFlexibility.Radial
