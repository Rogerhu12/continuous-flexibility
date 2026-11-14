module

public import ContinuousFlexibility.Analysis.WholePositiveEndpointFields
public import ContinuousFlexibility.Analysis.N04bPositiveDivision

/-!
# Positive source functions are unchanged by interior division

The interior completion changes only the stored divided coefficient.
These equalities retain the complete source functions, including their
endpoint selection, before applying any spatial derivative or bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem n04PositiveSourceMap_withInteriorDivision
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (K : CanonicalData S)
    (z : AnnularState S × ℝ) :
    n04PositiveSourceMap j (n04bWithInteriorDivision C K) z =
      n04PositiveSourceMap j K z := by
  rcases j with ⟨o, ho⟩
  cases o <;> rfl

theorem n04PositiveSourceHeight_withInteriorDivision
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (K : CanonicalData S)
    (z : AnnularState S × ℝ) :
    n04PositiveSourceHeight j (n04bWithInteriorDivision C K) z =
      n04PositiveSourceHeight j K z := by
  rcases j with ⟨o, ho⟩
  cases o <;> rfl

end ContinuousFlexibility.Analysis
