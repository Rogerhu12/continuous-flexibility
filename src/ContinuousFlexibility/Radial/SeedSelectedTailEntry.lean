import ContinuousFlexibility.Statements.RadialTargets

/-!
# Preparing the selected second mode without a first-band assumption

The frozen selection statement does not require its first frequency threshold
to exceed two. If that first band is empty, its entry field is unconstrained.
We set that entry to the actual selected band of mode two, preserving every
selection clause. If the first band is nonempty, uniqueness forces mode two
to belong to it and the update changes no entry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open Statements
open scoped Topology ContDiff

def seedSelectedTailAtBand (S : SelectedTailData) (n : ℕ) : SelectedTailData :=
  { S with entry := fun right m =>
      if m = S.chain.index then S.entry right n else S.entry right m }

theorem seedSelectedTailAtBand_self (S : SelectedTailData) :
    seedSelectedTailAtBand S S.chain.index = S := by
  have he : (fun right m => if m = S.chain.index then
      S.entry right S.chain.index else S.entry right m) = S.entry := by
    funext right m
    split_ifs with hm
    · subst m
      rfl
    · rfl
  unfold seedSelectedTailAtBand
  rw [he]

theorem first_band_contains_two_of_nonempty {S : SelectedTailData} {j : ℕ}
    (hj : 2 ≤ j) (hband : radialFrequencyBand S.chain S.Cstar S.chain.index j) :
    radialFrequencyBand S.chain S.Cstar S.chain.index 2 := by
  refine ⟨le_rfl, by norm_num, ?_⟩
  exact (by exact_mod_cast hj : (2 : ℝ) ≤ (j : ℝ)).trans_lt hband.2.2

theorem isSelectedTail_seedSelectedTailAtBand {S : SelectedTailData}
    (hS : IsSelectedTail S) {n : ℕ}
    (hband : radialFrequencyBand S.chain S.Cstar n 2) :
    IsSelectedTail (seedSelectedTailAtBand S n) := by
  by_cases hn : n = S.chain.index
  · subst n
    rw [seedSelectedTailAtBand_self]
    exact hS
  rcases hS with ⟨hC, hc, hσ, hfamily, hbands, hdata⟩
  have hno (j : ℕ) (hj : 2 ≤ j) :
      ¬ radialFrequencyBand S.chain S.Cstar S.chain.index j := by
    intro hjband
    obtain ⟨m, hm, huniq⟩ := hbands 2 (by omega) (by decide)
    have hi := huniq S.chain.index (first_band_contains_two_of_nonempty hj hjband)
    have hni := huniq n hband
    exact hn (hni.trans hi.symm)
  refine ⟨hC, hc, hσ, hfamily, hbands, ?_⟩
  intro right m j hj he hb
  have hm : m ≠ S.chain.index := by
    intro hm
    subst m
    exact hno j hj hb
  simpa [seedSelectedTailAtBand, hm] using hdata right m j hj he hb

/-- The same selected family, with its advertised innermost entry carrying
the actual natural second-mode solution. -/
theorem exists_seedSelectedTail_second_mode (hR07 : R07Statement) :
    ∃ S : SelectedTailData, IsSelectedTail S ∧
      ∀ right : Bool,
        S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
        RadialNaturalTail (S.family S.sigma) right 2
          (S.entry right S.chain.index) (S.outgoing right 2) := by
  obtain ⟨S, hS⟩ := hR07
  obtain ⟨n, hn, _⟩ := hS.2.2.2.2.1 2 (by omega) (by decide)
  refine ⟨seedSelectedTailAtBand S n, isSelectedTail_seedSelectedTailAtBand hS hn, ?_⟩
  intro right
  have hd := hS.2.2.2.2.2 right n 2 (by omega) (by decide) hn
  rcases hd with ⟨_, he, _, _, _, _, _, _, _, _, _, hnatural, _⟩
  simpa [seedSelectedTailAtBand] using And.intro he hnatural

end ContinuousFlexibility.Radial
