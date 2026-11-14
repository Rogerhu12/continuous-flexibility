module

public import ContinuousFlexibility.Radial.MatchedMorseCellWindows

/-!
# The true localizer after the retained coordinate change

The order isomorphism pulls each nonzero localizer back to its original
cell. Its two neighboring seams give an outer closed interval and an
inner exclusion. Comparing these intervals with an actual retained
piece bounds the two cell indices without splitting the two tails.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements

theorem matchedMorse_seams_order
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) {n : ℕ} (hn : T.index ≤ n) :
    morseChainSeam T false n < morseChainSeam T true n := by
  have hl := matchedMorse_oriented_seam_monotone hreal false le_rfl hn
  have hr := matchedMorse_oriented_seam_monotone hreal true le_rfl hn
  change -morseChainSeam T false T.index ≤ -morseChainSeam T false n at hl
  change morseChainSeam T true T.index ≤ morseChainSeam T true n at hr
  obtain ⟨_, _, _, _, _, hbase, _, _, _, _⟩ := hreal
  change morseChainSeam T false T.index < morseChainSeam T true T.index at hbase
  linarith only [hl, hr, hbase]

/-- A frozen localizer lies inside the outer pair of adjacent seams
and outside the open interval bounded by the inner pair. -/
theorem matchedMorse_localizer_nested_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool)
    {n : ℕ} (hn : T.index < n) {x : ℝ}
    (hx : x ∈ morseChainLocalizerRegion T D side n) :
    x ∈ Icc (morseChainSeam T false (n + 2)) (morseChainSeam T true (n + 2)) ∧
      (x ≤ morseChainSeam T false (n - 1) ∨ morseChainSeam T true (n - 1) ≤ x) := by
  have hw := matchedMorse_localizer_region_oriented_bounds hreal side hn hx
  have hn₀ : T.index ≤ n - 1 := by omega
  have hcross := matchedMorse_seams_order hreal hn₀
  have hl := matchedMorse_oriented_seam_monotone hreal false hn₀
    (show n - 1 ≤ n + 2 by omega)
  have hr := matchedMorse_oriented_seam_monotone hreal true hn₀
    (show n - 1 ≤ n + 2 by omega)
  change -morseChainSeam T false (n - 1) ≤ -morseChainSeam T false (n + 2) at hl
  change morseChainSeam T true (n - 1) ≤ morseChainSeam T true (n + 2) at hr
  cases side with
  | false =>
    change -morseChainSeam T false (n - 1) ≤ -x ∧
      -x ≤ -morseChainSeam T false (n + 2) at hw
    refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩ <;> linarith only [hw.1, hw.2, hcross, hr]
  | true =>
    change morseChainSeam T true (n - 1) ≤ x ∧
      x ≤ morseChainSeam T true (n + 2) at hw
    refine ⟨⟨?_, hw.2⟩, Or.inr hw.1⟩
    linarith only [hw.1, hcross, hl]

/-- The coordinate change acts on the actual localizer function.
No condition on the enlarged final cell sets is used. -/
theorem matchedMorse_pullback_localizer_nested_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C)
    (e : ℝ ≃o ℝ) (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m x, χ m x = D.localizer m (e x))
    {m : ℕ} (hm : T.index < D.cellIndex m) {x : ℝ} (hx : χ m x ≠ 0) :
    x ∈ Icc (e.symm (morseChainSeam T false (D.cellIndex m + 2)))
      (e.symm (morseChainSeam T true (D.cellIndex m + 2))) ∧
      (x ≤ e.symm (morseChainSeam T false (D.cellIndex m - 1)) ∨
        e.symm (morseChainSeam T true (D.cellIndex m - 1)) ≤ x) := by
  have hdata := hreal
  obtain ⟨_, _, _, _, _, _, _, hregions, _, hprofile⟩ := hdata
  have hxold : D.localizer m (e x) ≠ 0 := by
    rw [← hχ m x]
    exact hx
  have hcell : e x ∈ D.cells m := hprofile.2.1.2.2.1 m hxold
  obtain ⟨side, hside⟩ := hregions m hm
  have hb := matchedMorse_localizer_nested_bounds hreal side hm (hside hcell)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [e.symm_apply_apply] using e.symm.monotone hb.1.1
  · simpa only [e.symm_apply_apply] using e.symm.monotone hb.1.2
  · rcases hb.2 with hl | hr
    · exact Or.inl (by simpa only [e.symm_apply_apply] using e.symm.monotone hl)
    · exact Or.inr (by simpa only [e.symm_apply_apply] using e.symm.monotone hr)

/-- An actual piece between two nested seam pairs can intersect only
nearby localizer levels. The proof uses the two tails together. -/
theorem matchedMorse_nested_window_piece_index
    {L R : ℕ → ℝ} {N n m : ℕ} {x : ℝ}
    (hL : ∀ i j, N ≤ i → i ≤ j → L j ≤ L i)
    (hR : ∀ i j, N ≤ i → i ≤ j → R i ≤ R j)
    (hn : N < n) (hm : N ≤ m)
    (houter : x ∈ Icc (L (n + 2)) (R (n + 2)))
    (hinner : x ≤ L (n - 1) ∨ R (n - 1) ≤ x)
    (hpiece : x ∈ Ioo (L (m + 1)) (R (m + 1)))
    (hpieceOut : N < m → x < L (m - 1) ∨ R (m - 1) < x) :
    n - 1 ≤ m ∧ m ≤ n + 2 := by
  constructor
  · by_contra h
    have hij : m + 1 ≤ n - 1 := by omega
    have hl := hL (m + 1) (n - 1) (by omega) hij
    have hr := hR (m + 1) (n - 1) (by omega) hij
    rcases hinner with hlx | hrx
    · linarith only [hlx, hpiece.1, hl]
    · linarith only [hrx, hpiece.2, hr]
  · by_contra h
    have hij : n + 2 ≤ m - 1 := by omega
    have hl := hL (n + 2) (m - 1) (by omega) hij
    have hr := hR (n + 2) (m - 1) (by omega) hij
    rcases hpieceOut (by omega) with hlx | hrx
    · linarith only [hlx, houter.1, hl]
    · linarith only [hrx, houter.2, hr]

end ContinuousFlexibility.Radial
