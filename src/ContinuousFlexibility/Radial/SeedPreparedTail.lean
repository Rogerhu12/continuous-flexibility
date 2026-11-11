import ContinuousFlexibility.Radial.SeedMorseEntrance
import ContinuousFlexibility.Radial.MorseSecondModeLocalization

/-! # A selected second-mode pair with ordered regular entrances -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open Statements
open scoped ContDiff

theorem morseRealization_seams_order {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (hreal : MorseChainRealization T σ D C)
    {n : ℕ} (hn : T.index ≤ n) :
    morseChainSeam T false n < morseChainSeam T true n := by
  have hright (m : ℕ) (hm : T.index ≤ m) :
      morseChainSeam T true m < morseChainSeam T true (m + 1) := by
    exact (morseSecondMode_modelOrder hreal true hm).1.trans
      (morseSecondMode_gapOrder hreal hm true)
  have hleft (m : ℕ) (hm : T.index ≤ m) :
      morseChainSeam T false (m + 1) < morseChainSeam T false m := by
    exact (morseSecondMode_joinOrder hreal hm false).trans
      ((morseSecondMode_modelOrder hreal false hm).1.trans
        (morseSecondMode_modelOrder hreal false hm).2)
  have hbounds (k : ℕ) :
      morseChainSeam T false (T.index + k) ≤ morseChainSeam T false T.index ∧
      morseChainSeam T true T.index ≤ morseChainSeam T true (T.index + k) := by
    induction k with
    | zero => exact ⟨le_rfl, le_rfl⟩
    | succ k ih =>
      exact ⟨(hleft (T.index + k) (Nat.le_add_right _ _)).le.trans ih.1,
        ih.2.trans (hright (T.index + k) (Nat.le_add_right _ _)).le⟩
  have hfirst : morseChainSeam T false T.index < morseChainSeam T true T.index :=
    hreal.2.2.2.2.2.1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ((hbounds k).1.trans_lt hfirst).trans_le (hbounds k).2

/-- Keep the actual selected Morse band as well as its regular entrances.
The prepared entry need not be the original first seam. -/
theorem exists_seedPreparedSelectedTail_with_seams (hR07 : R07Statement) :
    ∃ S : SelectedTailData, IsSelectedTail S ∧ ∃ N : ℕ,
      S.chain.index ≤ N ∧
      (∀ right : Bool,
        S.entry right S.chain.index = morseChainSeam S.chain right N) ∧
      S.entry false S.chain.index < S.entry true S.chain.index ∧
      ∀ right : Bool,
        S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
        0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
        RadialNaturalTail (S.family S.sigma) right 2
          (S.entry right S.chain.index) (S.outgoing right 2) := by
  obtain ⟨S, hS⟩ := hR07
  obtain ⟨n, hn, _⟩ := hS.2.2.2.2.1 2 (by omega) (by decide)
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hdata (right : Bool) :=
    hS.2.2.2.2.2 right n 2 (by omega) (by decide) hn
  refine ⟨seedSelectedTailAtBand S n, isSelectedTail_seedSelectedTailAtBand hS hn,
    n, hn.1, ?_, ?_, ?_⟩
  · intro right
    simpa only [seedSelectedTailAtBand, if_pos rfl] using
      (hdata right).2.2.2.2.2.1
  · have hL := (hdata false).2.2.2.2.2.1
    have hR := (hdata true).2.2.2.2.2.1
    simp only [seedSelectedTailAtBand, if_pos rfl]
    rw [hL, hR]
    exact morseRealization_seams_order hreal hn.1
  · intro right
    rcases hdata right with ⟨_, he, _, _, _, hentry, _, _, _, _, _, hnatural, _⟩
    have hpos := morseRealization_seam_deriv_pos hreal hS.2.2.1 right hn.1
    have hpos' : 0 < deriv (S.family S.sigma).w (S.entry right n) := by
      rw [hentry]
      exact hpos
    simpa [seedSelectedTailAtBand] using
      And.intro he (And.intro hpos' hnatural)

theorem exists_seedPreparedSelectedTail (hR07 : R07Statement) :
    ∃ S : SelectedTailData, IsSelectedTail S ∧
      S.entry false S.chain.index < S.entry true S.chain.index ∧
      ∀ right : Bool,
        S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
        0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
        RadialNaturalTail (S.family S.sigma) right 2
          (S.entry right S.chain.index) (S.outgoing right 2) := by
  obtain ⟨S, hS, N, hN, hseams, horder, hentry⟩ :=
    exists_seedPreparedSelectedTail_with_seams hR07
  exact ⟨S, hS, horder, hentry⟩

end ContinuousFlexibility.Radial
