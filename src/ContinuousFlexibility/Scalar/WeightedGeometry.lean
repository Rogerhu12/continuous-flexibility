import ContinuousFlexibility.Scalar.WeightedGeometryLowJets
import ContinuousFlexibility.Scalar.WeightedStateFlatness

/-!
# Geometry of the actual weighted scalar state on one common ball

The radius depends on the fixed height centre and the given geometric data.
It is chosen once at input order four, before every output derivative order.
All smoothness, endpoint and positivity clauses are those of the frozen
`ScalarStateGeometry` definition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem exists_scalarStateBall_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (v₀ : ScalarHeightSpace S) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ x ∈ scalarStateBall S v₀ 4 ε, ScalarStateGeometry D S x := by
  obtain ⟨M, hM, hprofile⟩ := referenceProfile_uniform_upper_bound hD
  obtain ⟨Cχ, hCχ, hcutoff⟩ := scalarCutoff_deriv_le_reference hD hS
  obtain ⟨Cm, Cr, Ct, Ctt, hCm, hCr, hCt, hCtt, hmean, hradial, hangular, hsecond⟩ :=
    scalarHeight_low_jet_bounds hD hT hS
  obtain ⟨ε, hε, hεone, hpositive⟩ :=
    exists_scalarStateBall_positivity_of_low_jet_bounds hD hT hS v₀ 4
      Cm Cr Ct Ctt Cχ M hCm hCr hCt hCtt hCχ hM
      hprofile hmean hradial hangular hsecond hcutoff
  refine ⟨ε, hε, hεone, ?_⟩
  intro x hx
  have hend := scalarStateHeight_endpoint_values hD hT hS x
  refine ⟨scalarStateProfile_contDiff hD hT hS x,
    scalarStatePrimitive_contDiff hD hT hS x,
    scalarStateIncrement_contDiff hT hS x,
    scalarStatePrimitive_hasDerivAt hD hT hS x,
    fun _ hr => scalarStateProfile_eq_zero_outside hD x hr,
    scalarStateProfile_uniformFlatJets hD hT hS x,
    scalarStateDecodedHeight_uniformFlatJets hT hS x,
    hend.1, hend.2, ?_⟩
  intro r hr
  refine ⟨(hpositive x hx (r, 0) ⟨hr, mem_univ _⟩).1, fun θ => ?_⟩
  exact (hpositive x hx (r, θ) ⟨hr, mem_univ _⟩).2

end ContinuousFlexibility.Statements
