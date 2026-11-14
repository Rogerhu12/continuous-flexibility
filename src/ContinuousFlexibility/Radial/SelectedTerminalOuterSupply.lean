module

public import ContinuousFlexibility.Radial.MatchedPiecesAssembly

/-!
# The outer region on an unchanged matching shell

The actual outer construction installs its inverse, representative and
Poisson columns independently of the inner operator. Both frequency cases
use this same interface, after fixing their actual boundary data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- The outer construction does not inspect the installed inner operator. -/
def SelectedTerminalOuterSupply {D : ReferenceData} (M : RadialMatchingData D) : Prop :=
  ∀ (A : RadialModePair D →L[ℝ] RadialModePair D)
    (u : RadialModePair D → ℝ → ℝ),
    ∃ (R : RadialModePair D →L[ℝ] RadialModePair D)
      (v : RadialModePair D → ℝ → ℝ)
      (Q : Fin 2 → RadialModePair D) (p : Fin 2 → ℝ → ℝ),
      MatchingOuterRealizations D
        { M with
          innerInverse := A
          innerRepresentative := u
          outerInverse := R
          outerRepresentative := v
          outerPoisson := Q
          outerFunction := p }

end ContinuousFlexibility.Radial
