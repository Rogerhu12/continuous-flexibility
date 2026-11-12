import ContinuousFlexibility.Analysis.N04bOpticalFieldRealization

/-!
# The retained optical cutoff and cumulative physical construction

The existing factories choose one buffered cutoff and its actual source.
The supplied reference, material data, physical spaces, control geometry
and return-equation record are retained. The cutoff record is returned
with the complete cumulative certificate, so its numerical collar and
cutoff bounds remain available for later coordinate estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub

/-- Complete N03 and the raw field contract on the same fixed N01/N02
records. The returned field has the literal formulas for the one returned
cutoff; the neighborhood is selected once before any later jet order. -/
theorem n04Realization_exists_opticalField_through03
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ base' : ℕ, ∃ η : ℝ, base ≤ base' ∧ 0 < η ∧ η ≤ ε ∧
      ∃ Q : N04bOpticalCutoffData D S C base' η,
      ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
        NonlinearPropertiesThrough03 D T S C R (Q.field E) base' loss η ∧
        N04bFieldRegularity D S C (Q.field E) base' η ∧
        (Q.field E).coefficients = returnCorrectedCoefficients D S C Q.cutoff ∧
        (Q.field E).minusFlow = returnCorrectedMinusFlow S C Q.cutoff := by
  obtain ⟨base', η, hb, hη, hηε, hN', ⟨Q⟩⟩ :=
    hN.exists_n04b_opticalCutoffData hS hT
  have hR' : N02Properties D T S C R base' η :=
    hR.restrict_neighborhood hb hηε
  obtain ⟨E, h03, hfield⟩ := Q.exists_field hN' hS hT hR'
  exact ⟨base', η, hb, hη, hηε, Q, E, ⟨⟨hN', hR'⟩, h03⟩, hfield, rfl, rfl⟩

end ContinuousFlexibility.Analysis
