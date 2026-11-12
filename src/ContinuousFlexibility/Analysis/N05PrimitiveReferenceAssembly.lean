import ContinuousFlexibility.Analysis.N05PrimitiveReferenceCoordinates

/-!
# Controlled coordinates from the primitive N04 certificate

The Through04 certificate carries both primitive geometry bundles on the
same nonlinear witness. Reference radiality and reference jets from its
first bundle provide the inputs to the existing coordinate estimate,
without changing the canonical data or any of its charts.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

/-- Extract the explicit numerical-helper inputs from the accepted
Through04 witness, without changing any of its geometric data. -/
theorem n05_controlledReferenceCoordinates_of_primitive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (acceptedThrough04 : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    N05ControlledReferenceCoordinates D S C K := by
  have h01 : N01Properties D T S C base loss ε := acceptedThrough04.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := acceptedThrough04.2.2.2.2.1
  have hprimitive : CanonicalGeometry.PrimitiveGeometryProperties D T S C L K base ε :=
    acceptedThrough04.2.2.2.2.2.1
  exact n05_controlledReferenceCoordinates_of_referenceJets hD hT h01 h04
    hprimitive.1 hprimitive.2.2.1

end ContinuousFlexibility.Statements
