module

public import ContinuousFlexibility.Analysis.SpacesAssembly
public import ContinuousFlexibility.Analysis.SpacesPhysicalRetraction
public import ContinuousFlexibility.Analysis.SpacesNemytskiiSmooth

/-!
# The exact weighted-space statement

The concrete physical and circle retractions, all prescribed decoded
operations, and the full smooth-composition tower supply every clause of W02.
-/

@[expose] public section

namespace ContinuousFlexibility.Statements

/-- The complete W02 statement, with its original material-data hypotheses. -/
theorem spaces_W02_statement (hH01 : H01Statement) : W02Statement := by
  intro D T hD hT
  exact spaces_exists_physical_spaces_of_composition hD hT hH01
    (spacesPhysical_tameRetraction hT) (spaces_nemytskii_composition hT)

end ContinuousFlexibility.Statements
