import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# The qualitative coordinate clauses of the actual N04 construction

The reusable coordinate identities take the independently named qualitative
parts. They are literal conjuncts of the frozen cumulative N04 properties.
No coordinate witness is replaced by these projections.
-/

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Blueprint

theorem n06_N04_qualitative_parts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ} (h : N04Properties D T S C L K base loss ε) :
    N04PartA D S C K base ε ∧ N04PartB S C L K base ε := by
  obtain ⟨hopen, hsupport, hfixed, hpieces, hpositive, hnegative, hcover,
    hcharts, hboundary, hparity, hinverse, hcut, htransmission, hoperator,
    hnegativeForm, hcubic, _, _⟩ := h
  exact ⟨⟨hopen, hsupport, hfixed, hpieces, hpositive, hnegative, hcover,
      hcharts, hboundary, hparity, hinverse⟩,
    ⟨hcut, htransmission, hoperator, hnegativeForm, hcubic⟩⟩

end ContinuousFlexibility.Statements
