import ContinuousFlexibility.Analysis.MorsePositiveGapCells
import ContinuousFlexibility.Analysis.MorseRealizationComponentOrder
import ContinuousFlexibility.Radial.R11aRetainedFamily
import ContinuousFlexibility.Radial.SelectedSideTransport

/-!
# Exact retained coordinates on a whole positive Morse gap

The two actual turning roots belong to the same original tail. The
closed interval between them therefore remains in that tail. The
retained order isomorphism is exactly the existing radius dilation
there, so its original cell inclusion and index floor apply unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- Both caps and the join of the actual positive gap remain in the
original outward tail, including its two turning roots. -/
theorem morseRealization_positive_gap_subset_tail
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    Icc (n06MorsePositiveLeft T side n) (n06MorsePositiveRight T side n) ⊆
      radialTailInterval D side (morseChainSeam T side T.index) := by
  let d : ℕ := if side then n else n + 1
  let a : ℕ := if side then n + 1 else n
  have hd : T.index ≤ d := by
    cases side
    · exact hn.trans (Nat.le_succ n)
    · exact hn
  have ha : T.index ≤ a := by
    cases side
    · exact hn
    · exact hn.trans (Nat.le_succ n)
  have hturn (k : ℕ) (hk : T.index ≤ k) :
      T.radius side k (morseLeftTurn (morseChainA T k) (morseChainB T k)) ≤
        T.radius side k (morseRightTurn (morseChainA T k) (morseChainB T k)) := by
    obtain ⟨hl, hab, hu⟩ := morseRealization_turns_retained hreal side hk
    exact ((hreal.radius_strictMonoOn side k hk)
      ⟨hl.le, (hab.trans hu).le⟩ ⟨(hl.trans hab).le, hu.le⟩ hab).le
  have htail := (morseRealization_turning_component_order hreal).2.2
  have hl := htail side d hd (right_mem_Icc.mpr (hturn d hd))
  have hu := htail side a ha (left_mem_Icc.mpr (hturn a ha))
  change n06MorsePositiveLeft T side n ∈
    radialTailInterval D side (morseChainSeam T side T.index) at hl
  change n06MorsePositiveRight T side n ∈
    radialTailInterval D side (morseChainSeam T side T.index) at hu
  intro r hr
  cases side <;> exact ⟨hl.1.trans_le hr.1, hr.2.trans_lt hu.2⟩

/-- The actual retained-coordinate certificate supplies precisely the
cell dilation and index inequality needed by the material estimate.
No cell containing the entire positive gap is required. -/
theorem retainedReference_positive_gap_cell_transport
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    {Γ : ConnectedReferenceGeometry} (hcoordinates : R11aRetainedCoordinates P Γ) :
    (∀ (side : Bool) (n : ℕ), S.chain.index ≤ n → ∀ m r,
      r ∈ Icc (n06MorsePositiveLeft S.chain side n)
        (n06MorsePositiveRight S.chain side n) →
      r ∈ (S.family S.sigma).cells m →
      P.sideRadius side * r ∈ Γ.reference.cells m) ∧
    (∀ m, (S.family S.sigma).cellIndex m ≤ Γ.reference.cellIndex m) := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hseam (side : Bool) :
      S.entry side S.chain.index = morseChainSeam S.chain side S.chain.index := by
    simpa only [morseChainSeam] using
      (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hband).2.2.2.2.2.1
  obtain ⟨e, N, _, hlabels, hindex, hcells, _, hleft, hright, _, _, _⟩ :=
    hcoordinates
  constructor
  · intro side n hn m r hr hrm
    have ht := morseRealization_positive_gap_subset_tail hreal side hn hr
    have he : e.symm r = P.sideRadius side * r := by
      cases side
      · apply hleft r
        rw [hseam false]
        exact ht.2.le
      · apply hright r
        rw [hseam true]
        exact ht.1.le
    apply hcells m
    change e (P.sideRadius side * r) ∈ (S.family S.sigma).cells m
    rw [← he, e.apply_symm_apply]
    exact hrm
  · intro m
    rw [hlabels, hindex]
    exact Nat.le_max_left _ _

end ContinuousFlexibility.Radial
