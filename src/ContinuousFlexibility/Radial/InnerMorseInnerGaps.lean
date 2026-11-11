import ContinuousFlexibility.Radial.InnerMorseInnerChain
import ContinuousFlexibility.Radial.InnerModelChainGaps

/-!
# Exact pieces of the actual finite inner gap family

The enumeration distinguishes the two terminal cap remnants, the two
fixed central connectors, and the complete intervening Morse gaps.
All endpoint identities refer to the same previously constructed chain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

def innerMorseTerminalGapSlot (K : ℕ) (side : Bool) : Fin (2 * K + 2) :=
  if side then Fin.last (2 * K + 1) else 0

def innerMorseMiddleGapSlot (K : ℕ) (side : Bool) : Fin (2 * K + 2) :=
  if side then ⟨K + 1, by omega⟩ else ⟨K, by omega⟩

def innerMorseTailGapSlot (K : ℕ) (side : Bool) (p : Fin (K - 1)) : Fin (2 * K + 2) :=
  if side then ⟨K + 2 + p.val, by omega⟩ else ⟨p.val + 1, by omega⟩

def innerMorseTailGapCell (N K : ℕ) (side : Bool) (p : Fin (K - 1)) : ℕ :=
  if side then N + p.val else N + (K - 2 - p.val)

def innerMorseMiddleGapLeft (T : MorseChainData) (N : ℕ) (center : Fin 2 → ℝ)
    (side : Bool) : ℝ := if side then center 1 else innerMorseChainCut T false N 1

def innerMorseMiddleGapRight (T : MorseChainData) (N : ℕ) (center : Fin 2 → ℝ)
    (side : Bool) : ℝ := if side then innerMorseChainCut T true N 0 else center 0

theorem innerMorseInnerGap_cases {K : ℕ} (hK : 0 < K) (g : Fin (2 * K + 2)) :
    (∃ side, g = innerMorseTerminalGapSlot K side) ∨
      (∃ side, g = innerMorseMiddleGapSlot K side) ∨
      ∃ side p, g = innerMorseTailGapSlot K side p := by
  by_cases hg0 : g.val = 0
  · left
    refine ⟨false, ?_⟩
    apply Fin.ext
    simpa only [innerMorseTerminalGapSlot, Bool.false_eq_true, ite_false, Fin.val_zero] using hg0
  by_cases hgl : g.val = 2 * K + 1
  · left
    refine ⟨true, ?_⟩
    apply Fin.ext
    simpa only [innerMorseTerminalGapSlot, ite_true, Fin.val_last] using hgl
  by_cases hgK : g.val = K
  · right; left
    refine ⟨false, ?_⟩
    exact Fin.ext hgK
  by_cases hgK1 : g.val = K + 1
  · right; left
    refine ⟨true, ?_⟩
    exact Fin.ext hgK1
  right; right
  by_cases hleft : g.val < K
  · refine ⟨false, ⟨g.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false] <;> omega
  · refine ⟨true, ⟨g.val - K - 2, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [innerMorseTailGapSlot, ite_true] <;> omega

section ChainEndpoints

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
  (h : MorseChainRealization T σ D C) {N K : ℕ} (hN : T.index ≤ N) (hK : 0 < K)
  (center : Fin 2 → ℝ) (hc : center 0 < center 1)
  (hcl : innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < innerMorseChainCut T true N 0)

theorem innerMorseInnerChainGeometry_gap_left (g : Fin (2 * K + 2)) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left (innerModelChainGap g) =
      if hg : 0 < g.val then
        innerMorseInnerModelCuts T N K center ⟨g.val - 1, by omega⟩ 1
      else innerMorseInnerOuterPoint T N K false :=
  innerModelChainCuts_gap_left (innerMorseInnerModelCuts T N K center)
    (innerMorseInnerOuterPoint T N K false) (innerMorseInnerOuterPoint T N K true) g

theorem innerMorseInnerChainGeometry_gap_right (g : Fin (2 * K + 2)) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right (innerModelChainGap g) =
      if hg : g.val < 2 * K + 1 then
        innerMorseInnerModelCuts T N K center ⟨g.val, hg⟩ 0
      else innerMorseInnerOuterPoint T N K true :=
  innerModelChainCuts_gap_right (innerMorseInnerModelCuts T N K center)
    (innerMorseInnerOuterPoint T N K false) (innerMorseInnerOuterPoint T N K true) g

/-- The two terminal pieces are exactly the original outer cap remnants. -/
theorem innerMorseInnerChainGeometry_terminal (side : Bool) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left
        (innerModelChainGap (innerMorseTerminalGapSlot K side)) =
      T.radius side (N + (K - 1))
        (innerMorseOuterCapStart (morseChainA T (N + (K - 1)))
          (morseChainB T (N + (K - 1))) side) ∧
      (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right
        (innerModelChainGap (innerMorseTerminalGapSlot K side)) =
      T.radius side (N + (K - 1))
        (innerMorseOuterCapEnd (morseChainA T (N + (K - 1)))
          (morseChainB T (N + (K - 1))) side) := by
  have hm : T.index ≤ N + (K - 1) := hN.trans (Nat.le_add_right _ _)
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints h side hm
  rw [innerMorseInnerChainGeometry_gap_left, innerMorseInnerChainGeometry_gap_right]
  cases side with
  | false =>
    constructor <;> simp only [innerMorseTerminalGapSlot, Bool.false_eq_true, ite_false, Fin.val_zero,
      lt_self_iff_false, dite_false, Nat.zero_lt_succ, dite_true, innerMorseInnerModelCuts,
      hK, ite_true, Nat.sub_zero, innerMorseInnerOuterPoint, innerMorseOuterCapStart,
      innerMorseOuterCapEnd, innerMorseChainCut_zero, hl]
  | true =>
    have hlt : ¬2 * K < K := by omega
    have hne : 2 * K ≠ K := by omega
    have hidx : 2 * K - K - 1 = K - 1 := by omega
    constructor <;> simp only [innerMorseTerminalGapSlot, ite_true, Fin.val_last, Nat.zero_lt_succ,
      lt_self_iff_false, dite_true, dite_false, Nat.add_one_sub_one,
      innerMorseInnerModelCuts, hlt, hne, ite_false, hidx, innerMorseInnerOuterPoint,
      innerMorseOuterCapStart, innerMorseOuterCapEnd, innerMorseChainCut_one, hr]

theorem innerMorseInnerChainGeometry_middle (side : Bool) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left
        (innerModelChainGap (innerMorseMiddleGapSlot K side)) =
      innerMorseMiddleGapLeft T N center side ∧
      (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right
        (innerModelChainGap (innerMorseMiddleGapSlot K side)) =
      innerMorseMiddleGapRight T N center side := by
  have hg0 : 0 < (innerMorseMiddleGapSlot K side).val := by
    cases side <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hgm : (innerMorseMiddleGapSlot K side).val < 2 * K + 1 := by
    cases side <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [innerMorseInnerChainGeometry_gap_left, innerMorseInnerChainGeometry_gap_right,
    dif_pos hg0, dif_pos hgm]
  cases side with
  | false =>
    have hprev : K - 1 < K := by omega
    constructor <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false,
      innerMorseMiddleGapLeft, innerMorseMiddleGapRight, innerMorseInnerModelCuts,
      hprev, ite_true, Nat.sub_self, Nat.add_zero, lt_self_iff_false]
  | true =>
    have hnext : ¬K + 1 < K := by omega
    have hnextne : K + 1 ≠ K := by omega
    constructor <;> simp only [innerMorseMiddleGapSlot, ite_true, innerMorseMiddleGapLeft,
      innerMorseMiddleGapRight, innerMorseInnerModelCuts, Nat.add_one_sub_one,
      lt_self_iff_false, ite_false, hnext, hnextne, Nat.add_sub_cancel_left,
      Nat.sub_self, Nat.add_zero]

/-- Every interior tail gap is the same full cap-join-cap interval
already used in the uniform physical coercivity theorem. -/
theorem innerMorseInnerChainGeometry_tailGap (side : Bool) (p : Fin (K - 1)) :
    (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).left
        (innerModelChainGap (innerMorseTailGapSlot K side p)) =
      innerMorseTailGapLeft T side (innerMorseTailGapCell N K side p) ∧
      (innerMorseInnerChainGeometry h hN hK center hc hcl hcr).right
        (innerModelChainGap (innerMorseTailGapSlot K side p)) =
      innerMorseTailGapRight T side (innerMorseTailGapCell N K side p) := by
  have hg0 : 0 < (innerMorseTailGapSlot K side p).val := by
    cases side <;> simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hgm : (innerMorseTailGapSlot K side p).val < 2 * K + 1 := by
    cases side <;> simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [innerMorseInnerChainGeometry_gap_left, innerMorseInnerChainGeometry_gap_right,
    dif_pos hg0, dif_pos hgm]
  cases side with
  | false =>
    have hp0 : p.val < K := by omega
    have hp1 : p.val + 1 < K := by omega
    have hidx0 : N + (K - 1 - p.val) = N + (K - 2 - p.val) + 1 := by omega
    have hidx1 : K - 1 - (p.val + 1) = K - 2 - p.val := by omega
    constructor <;> simp only [innerMorseTailGapSlot, innerMorseTailGapCell, Bool.false_eq_true, ite_false,
      innerMorseTailGapLeft, innerMorseTailGapRight, innerMorseTailDeparture,
      innerMorseTailArrival, innerMorseInnerModelCuts, Nat.add_one_sub_one,
      hp0, hp1, ite_true, hidx0, hidx1]
  | true =>
    have hp0 : ¬K + 2 + p.val - 1 < K := by omega
    have hp1 : ¬K + 2 + p.val < K := by omega
    have hne0 : K + 2 + p.val - 1 ≠ K := by omega
    have hne1 : K + 2 + p.val ≠ K := by omega
    have hidx0 : K + 2 + p.val - 1 - K - 1 = p.val := by omega
    have hidx1 : N + (K + 2 + p.val - K - 1) = N + p.val + 1 := by omega
    constructor <;> simp only [innerMorseTailGapSlot, innerMorseTailGapCell, ite_true,
      innerMorseTailGapLeft, innerMorseTailGapRight, innerMorseTailDeparture,
      innerMorseTailArrival, innerMorseInnerModelCuts, hp0, hp1, hne0, hne1, ite_false,
      hidx0, hidx1]

end ChainEndpoints

end ContinuousFlexibility.Radial
