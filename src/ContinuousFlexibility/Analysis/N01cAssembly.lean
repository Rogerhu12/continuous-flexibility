module

public import ContinuousFlexibility.Blueprint.Statements

/-!
# Exact assembly of the N01 geometric and tame clauses

The theorem below only assembles estimates that have already been proved
for the same data and the same neighbourhood.  It proves no existence of
coefficient or flow estimates and is not a replacement for the N01c leaves.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem n01Properties_of_parts {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base loss : ℕ} {ε : ℝ}
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hCoefficients : CoefficientFamilyTameBounds D T S C base loss ε)
    (hFlows : OrdinaryFlowFamilyTameBounds T S C base loss ε) :
    N01Properties D T S C base loss ε := by
  obtain ⟨hD, hReference, hControl, hIndex, hControlBounds⟩ := hA
  obtain ⟨hFlow, hLeftChart, hInverses, hDenominators, hProfile⟩ := hB
  exact ⟨hD, hε, hReference, hControl, hIndex, hControlBounds, hFlow,
    hLeftChart, hInverses, hDenominators, hProfile, hCoefficients, hFlows⟩

end ContinuousFlexibility.Blueprint
