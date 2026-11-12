import ContinuousFlexibility.Radial.MatchedMorsePullbackWindows

/-!
# Physical cell and gap windows under the two true radius dilations

The same two positive scales act on every original tail cell.
Whole physical cells and their intervening gaps satisfy nested seam
bounds. These bounds apply to retained cuts by interval inclusion;
neither an inverse estimate nor a replacement geometry is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

section ScaledSeams

variable {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D C)
  (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)

local notation "L" => fun m => κ false * morseChainSeam T false m
local notation "R" => fun m => κ true * morseChainSeam T true m

include hreal hκ

theorem matchedScaledMorse_left_seam_antitone {m n : ℕ}
    (hm : T.index ≤ m) (hmn : m ≤ n) : L n ≤ L m := by
  have h := matchedMorse_oriented_seam_monotone hreal false hm hmn
  change -morseChainSeam T false m ≤ -morseChainSeam T false n at h
  exact mul_le_mul_of_nonneg_left (neg_le_neg_iff.mp h) (hκ false).le

theorem matchedScaledMorse_right_seam_monotone {m n : ℕ}
    (hm : T.index ≤ m) (hmn : m ≤ n) : R m ≤ R n := by
  have h := matchedMorse_oriented_seam_monotone hreal true hm hmn
  exact mul_le_mul_of_nonneg_left h (hκ true).le

theorem matchedScaledMorse_left_seam_succ_lt {m : ℕ}
    (hm : T.index ≤ m) : L (m + 1) < L m := by
  have h := matchedMorse_oriented_seam_succ_lt hreal false hm
  change -morseChainSeam T false m < -morseChainSeam T false (m + 1) at h
  exact mul_lt_mul_of_pos_left (neg_lt_neg_iff.mp h) (hκ false)

theorem matchedScaledMorse_right_seam_succ_lt {m : ℕ}
    (hm : T.index ≤ m) : R m < R (m + 1) := by
  exact mul_lt_mul_of_pos_left
    (matchedMorse_oriented_seam_succ_lt hreal true hm) (hκ true)

variable {N : ℕ} (hN : T.index ≤ N)
  (hcross : κ false * morseChainSeam T false N < κ true * morseChainSeam T true N)

include hN hcross

/-- Every original physical model cell, including both retained
endpoints, lies strictly between the next pair of outer seams. -/
theorem matchedScaledMorse_cell_nested_bounds
    (side : Bool) {m : ℕ} (hm : N ≤ m) {x : ℝ}
    (hx : x ∈ Icc (κ side * T.radius side m (T.leftX side m))
      (κ side * T.radius side m (T.rightX side m))) :
    x ∈ Ioo (L (m + 1)) (R (m + 1)) ∧
      (if side then R m ≤ x else x ≤ L m) := by
  have hleft := matchedScaledMorse_left_seam_antitone hreal κ hκ hN hm
  have hright := matchedScaledMorse_right_seam_monotone hreal κ hκ hN hm
  have hleftNext := matchedScaledMorse_left_seam_antitone hreal κ hκ hN
    (show N ≤ m + 1 by omega)
  have hrightNext := matchedScaledMorse_right_seam_monotone hreal κ hκ hN
    (show N ≤ m + 1 by omega)
  cases side with
  | false =>
    have hj := morseSecondMode_joinOrder hreal (hN.trans hm) false
    change morseChainSeam T false (m + 1) < T.radius false m (T.leftX false m) at hj
    have hj' := mul_lt_mul_of_pos_left hj (hκ false)
    have hxright : x ≤ L m := hx.2
    exact ⟨⟨hj'.trans_le hx.1, hxright.trans_lt (hleft.trans_lt
      (hcross.trans_le hrightNext))⟩, hxright⟩
  | true =>
    have hj := morseSecondMode_joinOrder hreal (hN.trans hm) true
    change T.radius true m (T.rightX true m) < morseChainSeam T true (m + 1) at hj
    have hj' := mul_lt_mul_of_pos_left hj (hκ true)
    have hxleft : R m ≤ x := hx.1
    exact ⟨⟨(hleftNext.trans_lt (hcross.trans_le hright)).trans_le hxleft,
      hx.2.trans_lt hj'⟩, hxleft⟩

/-- Passing from a cell to any strictly earlier seam makes the
outward exclusion strict, even at a physical model endpoint. -/
theorem matchedScaledMorse_cell_outside_previous
    (side : Bool) {m : ℕ} (hm : N < m) {x : ℝ}
    (hx : x ∈ Icc (κ side * T.radius side m (T.leftX side m))
      (κ side * T.radius side m (T.rightX side m))) :
    x < L (m - 1) ∨ R (m - 1) < x := by
  have hb := (matchedScaledMorse_cell_nested_bounds hreal κ hκ hN hcross side hm.le hx).2
  have hm₀ : 0 < m := by omega
  cases side with
  | false =>
    have hs := matchedScaledMorse_left_seam_succ_lt hreal κ hκ
      (show T.index ≤ m - 1 by omega)
    rw [Nat.sub_add_cancel hm₀] at hs
    exact Or.inl (hb.trans_lt hs)
  | true =>
    have hs := matchedScaledMorse_right_seam_succ_lt hreal κ hκ
      (show T.index ≤ m - 1 by omega)
    rw [Nat.sub_add_cancel hm₀] at hs
    exact Or.inr (hs.trans_le hb)

/-- A positive connector joins adjacent actual model cells. Its larger
cell index is m+1; both tail orientations have the same nested bounds. -/
theorem matchedScaledMorse_gap_nested_bounds
    (side : Bool) {m : ℕ} (hm : N ≤ m) {u v x : ℝ}
    (hu : u ∈ Icc
      (κ side * T.radius side (if side then m else m + 1)
        (T.leftX side (if side then m else m + 1)))
      (κ side * T.radius side (if side then m else m + 1)
        (T.rightX side (if side then m else m + 1))))
    (hv : v ∈ Icc
      (κ side * T.radius side (if side then m + 1 else m)
        (T.leftX side (if side then m + 1 else m)))
      (κ side * T.radius side (if side then m + 1 else m)
        (T.rightX side (if side then m + 1 else m))))
    (hx : x ∈ Ioo u v) :
    x ∈ Ioo (L (m + 2)) (R (m + 2)) ∧
      (x < L m ∨ R m < x) := by
  cases side with
  | false =>
    have hleft := matchedScaledMorse_cell_nested_bounds hreal κ hκ hN hcross false
      (show N ≤ m + 1 by omega) hu
    have hright := matchedScaledMorse_cell_nested_bounds hreal κ hκ hN hcross false hm hv
    have hR := matchedScaledMorse_right_seam_monotone hreal κ hκ
      (show T.index ≤ m + 1 by omega) (show m + 1 ≤ m + 2 by omega)
    refine ⟨⟨?_, ?_⟩, Or.inl (hx.2.trans_le hright.2)⟩
    · simpa only [Nat.add_assoc] using hleft.1.1.trans hx.1
    · exact hx.2.trans (hright.1.2.trans_le hR)
  | true =>
    have hleft := matchedScaledMorse_cell_nested_bounds hreal κ hκ hN hcross true hm hu
    have hright := matchedScaledMorse_cell_nested_bounds hreal κ hκ hN hcross true
      (show N ≤ m + 1 by omega) hv
    have hL := matchedScaledMorse_left_seam_antitone hreal κ hκ
      (show T.index ≤ m + 1 by omega) (show m + 1 ≤ m + 2 by omega)
    refine ⟨⟨?_, ?_⟩, Or.inr (hleft.2.trans_lt hx.1)⟩
    · exact (hL.trans_lt hleft.1.1).trans hx.1
    · simpa only [Nat.add_assoc] using hx.2.trans hright.1.2

end ScaledSeams

end ContinuousFlexibility.Radial
