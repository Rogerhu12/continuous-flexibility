import ContinuousFlexibility.Radial.MatchedMorsePieceWindows

/-!
# Nonzero localizers intersect only nearby original retained pieces

The same order isomorphism used to construct the final partition is
linear on the two retained tails. Hence the original scaled finite
chain and the actual pulled-back localizers have identical seam
coordinates. The initial finite labels are treated by one fixed
interior seam pair, before any retained length is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

theorem matchedMorse_linearTail_seams
    {T : MorseChainData} {σ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
    (h : MorseChainRealization T σ old cost) (e : ℝ ≃o ℝ) (κ : Bool → ℝ)
    {N : ℕ} (hN : T.index ≤ N)
    (he : ∀ side x, (if side then morseChainSeam T true N ≤ x
      else x ≤ morseChainSeam T false N) → e.symm x = κ side * x)
    (side : Bool) {m : ℕ} (hm : N ≤ m) :
    e.symm (morseChainSeam T side m) = κ side * morseChainSeam T side m := by
  apply he side _
  have hh := matchedMorse_oriented_seam_monotone h side hN hm
  cases side with
  | false =>
    change -morseChainSeam T false N ≤ -morseChainSeam T false m at hh
    exact neg_le_neg_iff.mp hh
  | true => exact hh

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
  (e : ℝ ≃o ℝ)
  (he : ∀ side x, (if side then morseChainSeam T true N ≤ x
    else x ≤ morseChainSeam T false N) → e.symm x = κ side * x)
  (hχ : ∀ m x, D.localizer m x = old.localizer m (e x))

local notation "G" => scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore

include he hχ

theorem matchedScaledMorse_localizer_piece_index
    {m : ℕ} (hm : N < old.cellIndex m)
    (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hχx : D.localizer m x ≠ 0)
    (hx : x ∈ Ioo ((G).left p) ((G).right p)) :
    old.cellIndex m - 1 ≤ innerMorseInnerPieceIndex N K p ∧
      innerMorseInnerPieceIndex N K p ≤ old.cellIndex m + 2 := by
  have hseam := matchedMorse_linearTail_seams h e κ hN he
  have hcross : κ false * morseChainSeam T false N < κ true * morseChainSeam T true N := by
    rw [← hseam false le_rfl, ← hseam true le_rfl]
    exact e.symm.strictMono (matchedMorse_seams_order h hN)
  have hw := matchedMorse_pullback_localizer_nested_bounds h e D.localizer hχ
    (hN.trans_lt hm) hχx
  rw [hseam false (show N ≤ old.cellIndex m + 2 by omega),
    hseam true (show N ≤ old.cellIndex m + 2 by omega),
    hseam false (show N ≤ old.cellIndex m - 1 by omega),
    hseam true (show N ≤ old.cellIndex m - 1 by omega)] at hw
  have hp := matchedScaledMorse_piece_nested_bounds h κ hκ hN hc hcl hcr D hD hK
    hLcore hRcore hcross p hx
  exact matchedMorse_nested_window_piece_index
    (fun i j hi hij => matchedScaledMorse_left_seam_antitone h κ hκ (hN.trans hi) hij)
    (fun i j hi hij => matchedScaledMorse_right_seam_monotone h κ hκ (hN.trans hi) hij)
    hm (innerMorseInnerPieceIndex_bounds N K p).1 hw.1 hw.2 hp.1 hp.2

/-- A fixed original interior seam pair also bounds all actual piece
indices met by an initial localizer, uniformly in the retained length. -/
theorem matchedScaledMorse_initial_localizer_piece_index
    {J m : ℕ} (hJ : N ≤ J)
    (hwindow : ∀ x, D.localizer m x ≠ 0 →
      e x ∈ Icc (morseChainSeam T false J) (morseChainSeam T true J))
    (p : Fin (2 * (2 * K + 1) + 1)) {x : ℝ}
    (hχx : D.localizer m x ≠ 0)
    (hx : x ∈ Ioo ((G).left p) ((G).right p)) :
    innerMorseInnerPieceIndex N K p ≤ J + 1 := by
  have hseam := matchedMorse_linearTail_seams h e κ hN he
  have hcross : κ false * morseChainSeam T false N < κ true * morseChainSeam T true N := by
    rw [← hseam false le_rfl, ← hseam true le_rfl]
    exact e.symm.strictMono (matchedMorse_seams_order h hN)
  have hp := matchedScaledMorse_piece_nested_bounds h κ hκ hN hc hcl hcr D hD hK
    hLcore hRcore hcross p hx
  have hw := hwindow x hχx
  have hl : κ false * morseChainSeam T false J ≤ x := by
    simpa only [hseam false hJ, e.symm_apply_apply] using e.symm.monotone hw.1
  have hr : x ≤ κ true * morseChainSeam T true J := by
    simpa only [hseam true hJ, e.symm_apply_apply] using e.symm.monotone hw.2
  by_contra hbad
  have hij : J ≤ innerMorseInnerPieceIndex N K p - 1 := by omega
  have hleft := matchedScaledMorse_left_seam_antitone h κ hκ (hN.trans hJ) hij
  have hright := matchedScaledMorse_right_seam_monotone h κ hκ (hN.trans hJ) hij
  rcases hp.2 (by omega) with hpL | hpR
  · linarith only [hpL, hl, hleft]
  · linarith only [hpR, hr, hright]

end ActualChain

end ContinuousFlexibility.Radial
