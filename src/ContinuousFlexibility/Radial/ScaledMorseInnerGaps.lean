module

public import ContinuousFlexibility.Radial.ScaledMorseInnerGeometry
public import ContinuousFlexibility.Radial.InnerMorseInnerGaps

/-!
# Exact gaps after independent radius dilations

Each endpoint is computed from the same finite chain. The terminal and
tail gaps are scaled on their own side; the two middle gaps meet the
already fixed central model endpoints in the new radius coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements

def scaledMorseMiddleGapLeft (T : MorseChainData) (κ : Bool → ℝ)
    (N : ℕ) (center : Fin 2 → ℝ) (side : Bool) : ℝ :=
  if side then center 1 else κ false * innerMorseChainCut T false N 1

def scaledMorseMiddleGapRight (T : MorseChainData) (κ : Bool → ℝ)
    (N : ℕ) (center : Fin 2 → ℝ) (side : Bool) : ℝ :=
  if side then κ true * innerMorseChainCut T true N 0 else center 0

section ChainEndpoints

variable {T : MorseChainData} {σ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
  (h : MorseChainRealization T σ old cost) (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)
  {N K : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
  (hc : center 0 < center 1)
  (hcl : κ false * innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < κ true * innerMorseChainCut T true N 0)
  (D : ReferenceData) (hD : RadialProfileGeometry D) (hK : 0 < K)
  (hLcore : scaledMorseInnerOuterPoint T κ N K false ∈ radialCore D)
  (hRcore : scaledMorseInnerOuterPoint T κ N K true ∈ radialCore D)

theorem scaledMorseInnerChainGeometry_gap_left (g : Fin (2 * K + 2)) :
    (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).left (innerModelChainGap g) =
      if hg : 0 < g.val then
        scaledMorseInnerModelCuts T κ N K center ⟨g.val - 1, by omega⟩ 1
      else scaledMorseInnerOuterPoint T κ N K false :=
  innerModelChainCuts_gap_left (scaledMorseInnerModelCuts T κ N K center)
    (scaledMorseInnerOuterPoint T κ N K false) (scaledMorseInnerOuterPoint T κ N K true) g

theorem scaledMorseInnerChainGeometry_gap_right (g : Fin (2 * K + 2)) :
    (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).right (innerModelChainGap g) =
      if hg : g.val < 2 * K + 1 then
        scaledMorseInnerModelCuts T κ N K center ⟨g.val, hg⟩ 0
      else scaledMorseInnerOuterPoint T κ N K true :=
  innerModelChainCuts_gap_right (scaledMorseInnerModelCuts T κ N K center)
    (scaledMorseInnerOuterPoint T κ N K false) (scaledMorseInnerOuterPoint T κ N K true) g

/-- The two terminal pieces are exactly the original outer cap remnants. -/
theorem scaledMorseInnerChainGeometry_terminal (side : Bool) :
    (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).left
        (innerModelChainGap (innerMorseTerminalGapSlot K side)) =
      κ side * T.radius side (N + (K - 1))
        (innerMorseOuterCapStart (morseChainA T (N + (K - 1)))
          (morseChainB T (N + (K - 1))) side) ∧
      (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).right
        (innerModelChainGap (innerMorseTerminalGapSlot K side)) =
      κ side * T.radius side (N + (K - 1))
        (innerMorseOuterCapEnd (morseChainA T (N + (K - 1)))
          (morseChainB T (N + (K - 1))) side) := by
  have hm : T.index ≤ N + (K - 1) := hN.trans (Nat.le_add_right _ _)
  obtain ⟨hl, hr⟩ := innerMorseChain_retained_endpoints h side hm
  rw [scaledMorseInnerChainGeometry_gap_left, scaledMorseInnerChainGeometry_gap_right]
  cases side with
  | false =>
    constructor <;> simp only [innerMorseTerminalGapSlot, Bool.false_eq_true, ite_false, Fin.val_zero,
      lt_self_iff_false, dite_false, Nat.zero_lt_succ, dite_true, scaledMorseInnerModelCuts,
      hK, ite_true, Nat.sub_zero, scaledMorseInnerOuterPoint, innerMorseInnerOuterPoint, innerMorseOuterCapStart,
      innerMorseOuterCapEnd, innerMorseChainCut_zero, hl]
  | true =>
    have hlt : ¬2 * K < K := by omega
    have hne : 2 * K ≠ K := by omega
    have hidx : 2 * K - K - 1 = K - 1 := by omega
    constructor <;> simp only [innerMorseTerminalGapSlot, ite_true, Fin.val_last, Nat.zero_lt_succ,
      lt_self_iff_false, dite_true, dite_false, Nat.add_one_sub_one,
      scaledMorseInnerModelCuts, hlt, hne, ite_false, hidx, scaledMorseInnerOuterPoint, innerMorseInnerOuterPoint,
      innerMorseOuterCapStart, innerMorseOuterCapEnd, innerMorseChainCut_one, hr]

theorem scaledMorseInnerChainGeometry_middle (side : Bool) :
    (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).left
        (innerModelChainGap (innerMorseMiddleGapSlot K side)) =
      scaledMorseMiddleGapLeft T κ N center side ∧
      (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).right
        (innerModelChainGap (innerMorseMiddleGapSlot K side)) =
      scaledMorseMiddleGapRight T κ N center side := by
  have hg0 : 0 < (innerMorseMiddleGapSlot K side).val := by
    cases side <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hgm : (innerMorseMiddleGapSlot K side).val < 2 * K + 1 := by
    cases side <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [scaledMorseInnerChainGeometry_gap_left, scaledMorseInnerChainGeometry_gap_right,
    dif_pos hg0, dif_pos hgm]
  cases side with
  | false =>
    have hprev : K - 1 < K := by omega
    constructor <;> simp only [innerMorseMiddleGapSlot, Bool.false_eq_true, ite_false,
      scaledMorseMiddleGapLeft, scaledMorseMiddleGapRight, scaledMorseInnerModelCuts,
      hprev, ite_true, Nat.sub_self, Nat.add_zero, lt_self_iff_false]
  | true =>
    have hnext : ¬K + 1 < K := by omega
    have hnextne : K + 1 ≠ K := by omega
    constructor <;> simp only [innerMorseMiddleGapSlot, ite_true, scaledMorseMiddleGapLeft,
      scaledMorseMiddleGapRight, scaledMorseInnerModelCuts, Nat.add_one_sub_one,
      lt_self_iff_false, ite_false, hnext, hnextne, Nat.add_sub_cancel_left,
      Nat.sub_self, Nat.add_zero]

/-- Every interior tail gap is the same full cap-join-cap interval
already used in the uniform physical coercivity theorem. -/
theorem scaledMorseInnerChainGeometry_tailGap (side : Bool) (p : Fin (K - 1)) :
    (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).left
        (innerModelChainGap (innerMorseTailGapSlot K side p)) =
      κ side * innerMorseTailGapLeft T side (innerMorseTailGapCell N K side p) ∧
      (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).right
        (innerModelChainGap (innerMorseTailGapSlot K side p)) =
      κ side * innerMorseTailGapRight T side (innerMorseTailGapCell N K side p) := by
  have hg0 : 0 < (innerMorseTailGapSlot K side p).val := by
    cases side <;> simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hgm : (innerMorseTailGapSlot K side p).val < 2 * K + 1 := by
    cases side <;> simp only [innerMorseTailGapSlot, Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [scaledMorseInnerChainGeometry_gap_left, scaledMorseInnerChainGeometry_gap_right,
    dif_pos hg0, dif_pos hgm]
  cases side with
  | false =>
    have hp0 : p.val < K := by omega
    have hp1 : p.val + 1 < K := by omega
    have hidx0 : N + (K - 1 - p.val) = N + (K - 2 - p.val) + 1 := by omega
    have hidx1 : K - 1 - (p.val + 1) = K - 2 - p.val := by omega
    constructor <;> simp only [innerMorseTailGapSlot, innerMorseTailGapCell, Bool.false_eq_true, ite_false,
      innerMorseTailGapLeft, innerMorseTailGapRight, innerMorseTailDeparture,
      innerMorseTailArrival, scaledMorseInnerModelCuts, Nat.add_one_sub_one,
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
      innerMorseTailArrival, scaledMorseInnerModelCuts, hp0, hp1, hne0, hne1, ite_false,
      hidx0, hidx1]

end ChainEndpoints

end ContinuousFlexibility.Radial
