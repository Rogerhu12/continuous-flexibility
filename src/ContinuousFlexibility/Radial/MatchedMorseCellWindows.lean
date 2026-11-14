module

public import ContinuousFlexibility.Radial.MorseSecondModeLocalization
public import ContinuousFlexibility.Radial.MorseChainPartitionData

/-!
# Actual localizer windows in one outward orientation

Reflection gives one increasing seam coordinate for both physical
tails. The frozen localizer collar lies inside the two adjacent seams.
These statements concern the original nonzero localizers and remain
valid after an order-isomorphism pullback; saturated final cells are
not used to locate physical points.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

theorem matchedMorse_oriented_seam_succ_lt
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {n : ℕ} (hn : T.index ≤ n) :
    morsePartitionOrientation side (morseChainSeam T side n) <
      morsePartitionOrientation side (morseChainSeam T side (n + 1)) := by
  cases side
  · change -morseChainSeam T false n < -morseChainSeam T false (n + 1)
    exact neg_lt_neg ((morseSecondMode_joinOrder hreal hn false).trans
      ((morseSecondMode_modelOrder hreal false hn).1.trans
        (morseSecondMode_modelOrder hreal false hn).2))
  · exact (morseSecondMode_modelOrder hreal true hn).1.trans
      (morseSecondMode_gapOrder hreal hn true)

theorem matchedMorse_oriented_seam_monotone
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {n m : ℕ} (hn : T.index ≤ n) (hnm : n ≤ m) :
    morsePartitionOrientation side (morseChainSeam T side n) ≤
      morsePartitionOrientation side (morseChainSeam T side m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
      exact ih.trans (matchedMorse_oriented_seam_succ_lt hreal side (hn.trans hnm)).le

theorem matchedMorse_orientation_abs_sub (side : Bool) (x y : ℝ) :
    |morsePartitionOrientation side x - morsePartitionOrientation side y| = |x - y| := by
  cases side
  · change |-x - -y| = |x - y|
    rw [neg_sub_neg, abs_sub_comm]
  · rfl

/-- The frozen geometric collar has only one sixteenth of either
incident span, so the whole localizer lies between adjacent seams. -/
theorem matchedMorse_localizer_region_oriented_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {n : ℕ} (hn : T.index < n) {x : ℝ}
    (hx : x ∈ morseChainLocalizerRegion T D side n) :
    morsePartitionOrientation side x ∈
      Icc (morsePartitionOrientation side (morseChainSeam T side (n - 1)))
        (morsePartitionOrientation side (morseChainSeam T side (n + 2))) := by
  have hn0 : 0 < n := by omega
  have hprevIndex : T.index ≤ n - 1 := by omega
  have hprev := matchedMorse_oriented_seam_succ_lt hreal side hprevIndex
  have hnext := matchedMorse_oriented_seam_succ_lt hreal side (show T.index ≤ n + 1 by omega)
  rw [Nat.sub_add_cancel hn0] at hprev
  have hleft :
      morseChainSeamCollar T D side n ≤
        morsePartitionOrientation side (morseChainSeam T side n) -
          morsePartitionOrientation side (morseChainSeam T side (n - 1)) := by
    have hh : morseChainSeamCollar T D side n ≤
        |morseChainSeam T side n - morseChainSeam T side (n - 1)| := by
      have hh := (min_le_right
        (min (morseChainSeam T side n - D.a) (D.b - morseChainSeam T side n))
        (min |morseChainSeam T side n - morseChainSeam T side (n - 1)|
          |morseChainSeam T side (n + 1) - morseChainSeam T side n|)).trans
            (min_le_left _ _)
      simp only [morseChainSeamCollar, hn, ite_true]
      linarith only [hh, abs_nonneg
        (morseChainSeam T side n - morseChainSeam T side (n - 1))]
    rw [← matchedMorse_orientation_abs_sub side,
      abs_of_nonneg (sub_nonneg.mpr hprev.le)] at hh
    exact hh
  have hright :
      morseChainSeamCollar T D side (n + 1) ≤
        morsePartitionOrientation side (morseChainSeam T side (n + 2)) -
          morsePartitionOrientation side (morseChainSeam T side (n + 1)) := by
    have hh : morseChainSeamCollar T D side (n + 1) ≤
        |morseChainSeam T side (n + 2) - morseChainSeam T side (n + 1)| := by
      have hh := (min_le_right
        (min (morseChainSeam T side (n + 1) - D.a) (D.b - morseChainSeam T side (n + 1)))
        (min |morseChainSeam T side (n + 1) - morseChainSeam T side n|
          |morseChainSeam T side (n + 2) - morseChainSeam T side (n + 1)|)).trans
            (min_le_right _ _)
      simp only [morseChainSeamCollar, show T.index < n + 1 by omega, ite_true,
        Nat.add_sub_cancel]
      linarith only [hh, abs_nonneg
        (morseChainSeam T side (n + 2) - morseChainSeam T side (n + 1))]
    rw [← matchedMorse_orientation_abs_sub side,
      abs_of_nonneg (sub_nonneg.mpr hnext.le)] at hh
    exact hh
  have hwindow :
      morsePartitionOrientation side (morseChainSeam T side n) -
        morseChainSeamCollar T D side n ≤ morsePartitionOrientation side x ∧
      morsePartitionOrientation side x ≤
        morsePartitionOrientation side (morseChainSeam T side (n + 1)) +
          morseChainSeamCollar T D side (n + 1) := by
    cases side <;>
      simp only [morseChainLocalizerRegion, morsePartitionOrientation,
        Bool.false_eq_true, ite_false, ite_true, mem_Icc] at hx ⊢
    · constructor <;> linarith only [hx.1, hx.2]
    · exact hx
  constructor <;> linarith only [hleft, hright, hwindow.1, hwindow.2]

/-- A localizer window can meet only adjacent cells of an increasing
outward seam sequence. This lemma handles both tails after reflection. -/
theorem matchedMorse_window_cell_index {s : ℕ → ℝ} (hs : Monotone s)
    {m n : ℕ} {x : ℝ}
    (hwindow : x ∈ Icc (s (n - 1)) (s (n + 2)))
    (hcell : x ∈ Ioo (s m) (s (m + 1))) :
    n - 1 ≤ m ∧ m ≤ n + 1 := by
  constructor
  · by_contra h
    have hm : m + 1 ≤ n - 1 := by omega
    have hh := hs hm
    linarith only [hwindow.1, hcell.2, hh]
  · by_contra h
    have hm : n + 2 ≤ m := by omega
    have hh := hs hm
    linarith only [hwindow.2, hcell.1, hh]

end ContinuousFlexibility.Radial
