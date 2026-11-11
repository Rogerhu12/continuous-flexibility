import ContinuousFlexibility.Radial.OuterSeamRegions

/-!
# Reverse support bounds for a specified physical localizer

The realization supplies a containing region for the actual cell `m`.
Separation of the two chains identifies its side, and the collar geometry
then bounds its fixed physical label. No covering cell is substituted for
the localizer that appears in the estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem morseRealized_region_block_same_side {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (side right : Bool) {i p : ℕ} (hi : M.index < i) (hp : M.index ≤ p) {r : ℝ}
    (hr : r ∈ morseChainLocalizerRegion M D side i)
    (hb : r ∈ morseChainBlock M right p) : side = right := by
  have hreg := morseRealized_region_near_seams h side hi hr
  have hblock := (morseRealized_mem_block_iff_outward h right p hp r).mp hb
  have hpast : M.index ≤ i - 1 := by omega
  have hreghead := (morseRealized_outward_seam_strictMonoOn h side).monotoneOn
    (show M.index ∈ Ici M.index from by change M.index ≤ M.index; exact le_rfl) hpast hpast
  have hblockhead := (morseRealized_outward_seam_strictMonoOn h right).monotoneOn
    (show M.index ∈ Ici M.index from by change M.index ≤ M.index; exact le_rfl) hp hp
  have hR : outerOutwardRadius side (morseChainSeam M side M.index) <
      outerOutwardRadius side r := hreghead.trans_lt hreg.1
  have hB : outerOutwardRadius right (morseChainSeam M right M.index) ≤
      outerOutwardRadius right r := hblockhead.trans hblock.1
  have hgap : morseChainSeam M false M.index < morseChainSeam M true M.index :=
    h.2.2.2.2.2.1
  cases right with
  | false =>
      cases side with
      | false => rfl
      | true =>
          exfalso
          change morseChainSeam M true M.index < r at hR
          change -morseChainSeam M false M.index ≤ -r at hB
          linarith only [hR, hB, hgap]
  | true =>
      cases side with
      | false =>
          exfalso
          change -morseChainSeam M false M.index < -r at hR
          change morseChainSeam M true M.index ≤ r at hB
          linarith only [hR, hB, hgap]
      | true => rfl

/-- A region meeting block `p` has physical label between `p-1` and `p+1`. -/
theorem morseRealized_region_block_indices {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (side right : Bool) {i p : ℕ} (hi : M.index < i) (hp : M.index ≤ p) {r : ℝ}
    (hr : r ∈ morseChainLocalizerRegion M D side i)
    (hb : r ∈ morseChainBlock M right p) : p ≤ i + 1 ∧ i ≤ p + 1 := by
  have he := morseRealized_region_block_same_side h side right hi hp hr hb
  subst side
  have hreg := morseRealized_region_near_seams h right hi hr
  have hblock := (morseRealized_mem_block_iff_outward h right p hp r).mp hb
  have hmono := (morseRealized_outward_seam_strictMonoOn h right).monotoneOn
  constructor
  · by_contra hnot
    have hip : i + 2 ≤ p := by omega
    have hs := hmono (show M.index ≤ i + 2 by omega) hp hip
    linarith only [hreg.2, hblock.1, hs]
  · by_contra hnot
    have hpi : p + 1 ≤ i - 1 := by omega
    have hs := hmono (show M.index ≤ p + 1 by omega) (show M.index ≤ i - 1 by omega) hpi
    linarith only [hreg.1, hblock.2, hs]

/-- The label bound applies to the specified nonzero localizer itself. -/
theorem morseRealized_localizer_block_indices {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) {m p : ℕ} (hm : M.index < D.cellIndex m) (hp : M.index ≤ p)
    {r : ℝ} (hr : r ∈ morseChainBlock M right p) (hθ : D.localizer m r ≠ 0) :
    p ≤ D.cellIndex m + 1 ∧ D.cellIndex m ≤ p + 1 := by
  have hregions : ∀ m, M.index < D.cellIndex m → ∃ side : Bool,
      D.cells m ⊆ morseChainLocalizerRegion M D side (D.cellIndex m) := by
    rcases h with ⟨_, _, _, _, _, _, _, hc, _, _⟩
    exact hc
  obtain ⟨side, hs⟩ := hregions m hm
  have hpart : RadialPartition D := h.accumulating.2.1
  have hcell : r ∈ D.cells m := hpart.2.2.1 m hθ
  exact morseRealized_region_block_indices h side right hm hp (hs hcell) hr

end ContinuousFlexibility.Radial
