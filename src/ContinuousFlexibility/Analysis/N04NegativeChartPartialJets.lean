module

public import ContinuousFlexibility.Analysis.N01cFiniteAffineMixedJets

/-! Smoothness of the actual finite state jet with arbitrary external
normed variables. No estimate or extension is part of this interface. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04NegativeChart_partial_stateJet_contDiff
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : P × Q → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : P) (v : Fin k → P) :
    ContDiff ℝ ∞ (fun q => iteratedFDeriv ℝ k (fun y => f (y, q)) x v) := by
  let J : ∀ q : Q, SmoothDirections (univ : Set P) (fun y => f (y, q)) := fun q =>
    smoothDirectionsOfJets isOpen_univ
      (fun n => iteratedFDeriv ℝ n (fun y => f (y, q)))
      (hasProjectiveJetsOn_of_contDiffOn isOpen_univ
        (hf.comp (contDiff_id.prodMk contDiff_const)).contDiffOn)
  have hs := contDiffOn_stateJetEvaluation isOpen_univ isOpen_univ hf.contDiffOn J k v
  have hs' : ContDiffOn ℝ ∞ (fun q : Q => (J q).D k x v) univ :=
    hs.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  simpa only [J, smoothDirectionsOfJets, contDiffOn_univ] using hs'

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_partial_stateJet_contDiff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_partial_stateJet_contDiff
