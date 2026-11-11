import ContinuousFlexibility.Blueprint.R10a.Geometry
import ContinuousFlexibility.Radial.TerminalRegionalData

/-!
# R10a: regional inverses and terminal cutoff data on one geometry

This is the remaining analytic construction. The geometry supply fixes
one selected sequence before its freely chosen central window and cone
lengths. The output uses one reference at every frequency and records
actual weak inverse graphs and physical cutoff data. The inner Poisson
columns and their flux matrix are constructed separately.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem R10aRegional (hR06 : R06Statement) (hR09 : R09Statement)
    (hgeometry : R10aGeometrySupply) :
    ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
      RadialConstructionGeometry D ∧
      ∀ j : ℕ, 2 ≤ j → Even j →
        ∃ W : TerminalRegionalData D, W.matching.frequency = j := by
  sorry

end ContinuousFlexibility.Blueprint
