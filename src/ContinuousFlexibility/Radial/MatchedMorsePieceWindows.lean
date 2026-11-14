module

public import ContinuousFlexibility.Radial.MatchedScaledMorseWindows
public import ContinuousFlexibility.Radial.ScaledMorseInnerGaps
public import ContinuousFlexibility.Radial.InnerMorseInnerWeightCosts

/-!
# Original retained pieces have nearby physical cell labels

All intervals below are the original scaled finite-chain intervals.
The model cuts, central connectors, complete tail gaps and terminal
cap remnants are handled by their exact endpoint identities. This
provides the geometric input for extracting the actual signed weights
on the true nonzero localizers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

theorem matchedMorse_gapIndex_terminal (N K : ℕ) (side : Bool) :
    innerMorseInnerGapIndex N K (innerMorseTerminalGapSlot K side) = N + (K - 1) := by
  cases side with
  | false =>
    simp only [innerMorseInnerGapIndex, innerMorseTerminalGapSlot, Bool.false_eq_true,
      ite_false, Fin.val_zero, Nat.zero_le, ite_true, Nat.sub_zero]
    rw [Nat.min_eq_left (Nat.sub_le K 1)]
  | true =>
    have hgt : ¬2 * K + 1 ≤ K := by omega
    have he : 2 * K + 1 - K - 1 = K := by omega
    simp only [innerMorseInnerGapIndex, innerMorseTerminalGapSlot, ite_true,
      Fin.val_last, hgt, ite_false, he]
    rw [Nat.min_eq_left (Nat.sub_le K 1)]

theorem matchedMorse_gapIndex_middle (N K : ℕ) (side : Bool) :
    innerMorseInnerGapIndex N K (innerMorseMiddleGapSlot K side) = N := by
  cases side with
  | false =>
    simp only [innerMorseInnerGapIndex, innerMorseMiddleGapSlot, Bool.false_eq_true,
      ite_false, le_refl, ite_true, Nat.sub_self, Nat.min_zero, Nat.add_zero]
  | true =>
    have hgt : ¬K + 1 ≤ K := by omega
    simp only [innerMorseInnerGapIndex, innerMorseMiddleGapSlot, ite_true,
      hgt, ite_false, Nat.add_sub_cancel_left, Nat.sub_self, Nat.min_zero, Nat.add_zero]

theorem matchedMorse_gapIndex_tail (N K : ℕ) (side : Bool) (p : Fin (K - 1)) :
    innerMorseInnerGapIndex N K (innerMorseTailGapSlot K side p) =
      innerMorseTailGapCell N K side p + 1 := by
  cases side with
  | false =>
    have hle : p.val + 1 ≤ K := by omega
    have hmin : K - (p.val + 1) ≤ K - 1 := by omega
    simp only [innerMorseInnerGapIndex, innerMorseTailGapSlot, innerMorseTailGapCell,
      Bool.false_eq_true, ite_false, hle, ite_true, Nat.min_eq_right hmin]
    omega
  | true =>
    have hgt : ¬K + 2 + p.val ≤ K := by omega
    have he : K + 2 + p.val - K - 1 = p.val + 1 := by omega
    have hmin : p.val + 1 ≤ K - 1 := by omega
    simp only [innerMorseInnerGapIndex, innerMorseTailGapSlot, innerMorseTailGapCell,
      ite_true, hgt, ite_false, he, Nat.min_eq_right hmin]
    omega

theorem matchedScaledMorse_innerCut_mem_cell
    {T : MorseChainData} {σ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
    (h : MorseChainRealization T σ old cost) (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)
    (side : Bool) {m : ℕ} (hm : T.index ≤ m) (i : Fin 2) :
    κ side * innerMorseChainCut T side m i ∈
      Icc (κ side * T.radius side m (T.leftX side m))
        (κ side * T.radius side m (T.rightX side m)) := by
  have hb := innerMorseChainCut_geometry h side hm
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · exact ⟨mul_le_mul_of_nonneg_left hb.1.le (hκ side).le,
      mul_le_mul_of_nonneg_left (hb.2.1.trans hb.2.2.1).le (hκ side).le⟩
  · exact ⟨mul_le_mul_of_nonneg_left (hb.1.trans hb.2.1).le (hκ side).le,
      mul_le_mul_of_nonneg_left hb.2.2.1.le (hκ side).le⟩

section ActualChain

variable {T : MorseChainData} {σ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
  (h : MorseChainRealization T σ old cost) (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)
  {N K : ℕ} (hN : T.index ≤ N) {center : Fin 2 → ℝ}
  (hc : center 0 < center 1)
  (hcl : κ false * innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < κ true * innerMorseChainCut T true N 0)
  (D : ReferenceData) (hD : RadialProfileGeometry D) (hK : 0 < K)
  (hLcore : scaledMorseInnerOuterPoint T κ N K false ∈ radialCore D)
  (hRcore : scaledMorseInnerOuterPoint T κ N K true ∈ radialCore D)
  (hcross : κ false * morseChainSeam T false N < κ true * morseChainSeam T true N)

local notation "G" => scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore
local notation "L" => fun m => κ false * morseChainSeam T false m
local notation "R" => fun m => κ true * morseChainSeam T true m

include h hκ hN hc hcl hcr hcross

private theorem matchedScaledMorse_center_seams :
    L (N + 1) < center 0 ∧ center 1 < R (N + 1) := by
  have hl := matchedScaledMorse_cell_nested_bounds h κ hκ hN hcross false le_rfl
    (matchedScaledMorse_innerCut_mem_cell h κ hκ false hN 1)
  have hr := matchedScaledMorse_cell_nested_bounds h κ hκ hN hcross true le_rfl
    (matchedScaledMorse_innerCut_mem_cell h κ hκ true hN 0)
  exact ⟨hl.1.1.trans hcl, hcr.trans hr.1.2⟩

private theorem matchedScaledMorse_tail_piece_nested
    (side : Bool) (p : Fin K) {x : ℝ}
    (hx : x ∈ Ioo ((G).left (innerModelChainPiece (innerMorseInnerTailSlot K side p)))
      ((G).right (innerModelChainPiece (innerMorseInnerTailSlot K side p)))) :
    x ∈ Ioo (L (innerMorseInnerTailIndex N K side p + 1))
      (R (innerMorseInnerTailIndex N K side p + 1)) ∧
      (N < innerMorseInnerTailIndex N K side p →
        x < L (innerMorseInnerTailIndex N K side p - 1) ∨
          R (innerMorseInnerTailIndex N K side p - 1) < x) := by
  have he := scaledMorseInnerChainGeometry_tail h κ hκ hN hc hcl hcr D hD hK
    hLcore hRcore side p
  rw [he.1, he.2] at hx
  have hm := (innerMorseInnerTailIndex_bounds N K side p).1
  have hl := matchedScaledMorse_innerCut_mem_cell h κ hκ side (hN.trans hm) 0
  have hr := matchedScaledMorse_innerCut_mem_cell h κ hκ side (hN.trans hm) 1
  have hxcell : x ∈ Icc
      (κ side * T.radius side (innerMorseInnerTailIndex N K side p)
        (T.leftX side (innerMorseInnerTailIndex N K side p)))
      (κ side * T.radius side (innerMorseInnerTailIndex N K side p)
        (T.rightX side (innerMorseInnerTailIndex N K side p))) :=
    ⟨hl.1.trans hx.1.le, hx.2.le.trans hr.2⟩
  exact ⟨(matchedScaledMorse_cell_nested_bounds h κ hκ hN hcross side hm hxcell).1,
    fun hm' => matchedScaledMorse_cell_outside_previous h κ hκ hN hcross side hm' hxcell⟩

/-- Every actual retained piece uses its original neighboring cell
index. The central pieces have the fixed initial index. -/
theorem matchedScaledMorse_piece_nested_bounds
    (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hx : x ∈ Ioo ((G).left p) ((G).right p)) :
    x ∈ Ioo (L (innerMorseInnerPieceIndex N K p + 1))
      (R (innerMorseInnerPieceIndex N K p + 1)) ∧
      (N < innerMorseInnerPieceIndex N K p →
        x < L (innerMorseInnerPieceIndex N K p - 1) ∨
          R (innerMorseInnerPieceIndex N K p - 1) < x) := by
  have hcen := matchedScaledMorse_center_seams h κ hκ hN hc hcl hcr hcross
  rcases innerModelChainPiece_or_gap p with ⟨p, rfl⟩ | ⟨g, rfl⟩
  · by_cases hp : p.val < K
    · let r : Fin K := ⟨p.val, hp⟩
      have he : p = innerMorseInnerTailSlot K false r := Fin.ext rfl
      rw [he] at hx ⊢
      simpa only [innerMorseInnerPieceIndex_model, innerMorseInnerModelIndex_tail] using
        matchedScaledMorse_tail_piece_nested h κ hκ hN hc hcl hcr D hD hK
          hLcore hRcore hcross false r hx
    · by_cases hp₀ : p.val = K
      · have he : p = innerMorseInnerCenter K := Fin.ext hp₀
        rw [he] at hx ⊢
        rw [innerMorseInnerPieceIndex_model, innerMorseInnerModelIndex_center]
        have hh := scaledMorseInnerChainGeometry_center h κ hκ hN hc hcl hcr D hD hK
          hLcore hRcore
        rw [hh.1, hh.2] at hx
        exact ⟨⟨hcen.1.trans hx.1, hx.2.trans hcen.2⟩, fun hbad => (lt_irrefl _ hbad).elim⟩
      · let r : Fin K := ⟨p.val - K - 1, by omega⟩
        have he : p = innerMorseInnerTailSlot K true r := by
          apply Fin.ext
          simp only [innerMorseInnerTailSlot, ite_true, r]
          omega
        rw [he] at hx ⊢
        simpa only [innerMorseInnerPieceIndex_model, innerMorseInnerModelIndex_tail] using
          matchedScaledMorse_tail_piece_nested h κ hκ hN hc hcl hcr D hD hK
            hLcore hRcore hcross true r hx
  · rw [innerMorseInnerPieceIndex_gap]
    rcases innerMorseInnerGap_cases hK g with
      ⟨side, rfl⟩ | ⟨side, rfl⟩ | ⟨side, r, rfl⟩
    · rw [matchedMorse_gapIndex_terminal]
      have hm : N ≤ N + (K - 1) := Nat.le_add_right _ _
      have he := scaledMorseInnerChainGeometry_terminal h κ hκ hN hc hcl hcr D hD hK
        hLcore hRcore side
      have hend := innerMorseChain_retained_endpoints h side (hN.trans hm)
      have hxcell : x ∈ Icc
          (κ side * T.radius side (N + (K - 1)) (T.leftX side (N + (K - 1))))
          (κ side * T.radius side (N + (K - 1)) (T.rightX side (N + (K - 1)))) := by
        rw [he.1, he.2] at hx
        cases side with
        | false =>
          have hcut := matchedScaledMorse_innerCut_mem_cell h κ hκ false (hN.trans hm) 0
          have hl : κ false * T.radius false (N + (K - 1))
              (T.leftX false (N + (K - 1))) < x := by
            simpa only [innerMorseOuterCapStart, Bool.false_eq_true, ite_false, hend.1]
              using hx.1
          have hr : x < κ false * innerMorseChainCut T false (N + (K - 1)) 0 := by
            simpa only [innerMorseOuterCapEnd, Bool.false_eq_true, ite_false,
              innerMorseChainCut_zero] using hx.2
          exact ⟨hl.le, hr.le.trans hcut.2⟩
        | true =>
          have hcut := matchedScaledMorse_innerCut_mem_cell h κ hκ true (hN.trans hm) 1
          have hl : κ true * innerMorseChainCut T true (N + (K - 1)) 1 < x := by
            simpa only [innerMorseOuterCapStart, ite_true, innerMorseChainCut_one] using hx.1
          have hr : x < κ true * T.radius true (N + (K - 1))
              (T.rightX true (N + (K - 1))) := by
            simpa only [innerMorseOuterCapEnd, ite_true, hend.2] using hx.2
          exact ⟨hcut.1.trans hl.le, hr.le⟩
      exact ⟨(matchedScaledMorse_cell_nested_bounds h κ hκ hN hcross side hm hxcell).1,
        fun hm' => matchedScaledMorse_cell_outside_previous h κ hκ hN hcross side hm' hxcell⟩
    · rw [matchedMorse_gapIndex_middle]
      have he := scaledMorseInnerChainGeometry_middle h κ hκ hN hc hcl hcr D hD hK
        hLcore hRcore side
      rw [he.1, he.2] at hx
      refine ⟨?_, fun hbad => (lt_irrefl _ hbad).elim⟩
      cases side with
      | false =>
        change κ false * innerMorseChainCut T false N 1 < x ∧ x < center 0 at hx
        have hl := matchedScaledMorse_cell_nested_bounds h κ hκ hN hcross false le_rfl
          (matchedScaledMorse_innerCut_mem_cell h κ hκ false hN 1)
        exact ⟨hl.1.1.trans hx.1, hx.2.trans (hc.trans hcen.2)⟩
      | true =>
        change center 1 < x ∧ x < κ true * innerMorseChainCut T true N 0 at hx
        have hr := matchedScaledMorse_cell_nested_bounds h κ hκ hN hcross true le_rfl
          (matchedScaledMorse_innerCut_mem_cell h κ hκ true hN 0)
        exact ⟨(hcen.1.trans hc).trans hx.1, hx.2.trans hr.1.2⟩
    · rw [matchedMorse_gapIndex_tail]
      let m := innerMorseTailGapCell N K side r
      have hm : N ≤ m := by
        cases side <;> simp only [m, innerMorseTailGapCell, Bool.false_eq_true, ite_false,
          ite_true] <;> omega
      have he := scaledMorseInnerChainGeometry_tailGap h κ hκ hN hc hcl hcr D hD hK
        hLcore hRcore side r
      rw [he.1, he.2] at hx
      have hu := matchedScaledMorse_innerCut_mem_cell h κ hκ side
        (show T.index ≤ (if side then m else m + 1) by cases side <;> simp <;> omega) 1
      have hv := matchedScaledMorse_innerCut_mem_cell h κ hκ side
        (show T.index ≤ (if side then m + 1 else m) by cases side <;> simp <;> omega) 0
      have hh := matchedScaledMorse_gap_nested_bounds h κ hκ hN hcross side hm hu hv
        (show x ∈ Ioo (κ side * innerMorseChainCut T side (if side then m else m + 1) 1)
          (κ side * innerMorseChainCut T side (if side then m + 1 else m) 0) from hx)
      refine ⟨?_, fun _ => ?_⟩
      · simpa only [Nat.add_assoc] using hh.1
      · simpa only [Nat.add_sub_cancel] using hh.2

end ActualChain

end ContinuousFlexibility.Radial
