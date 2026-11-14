module

public import ContinuousFlexibility.Analysis.N04bOpticalCutoffProperties
public import ContinuousFlexibility.Analysis.N04bOpticalFieldType
public import ContinuousFlexibility.Analysis.N04bReferenceCorrection
public import ContinuousFlexibility.Analysis.N03CorrectionAssembly

/-!
# The literal optical correction satisfies the physical field contracts

The stored coefficients and flow are the actual cutoff formulas. Their
N03 equations and all five raw regularity fields use the same chosen
cutoff, including the strict corrected characteristic gap and the exact
reference flow. No regularity of an arbitrary stored coefficient field
is inferred from its operator action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

namespace N04bOpticalCutoffData

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)

def field
    (E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source) :
    ReturnCorrectionData S where
  coefficients := returnCorrectedCoefficients D S C Q.cutoff
  minusFlow := returnCorrectedMinusFlow S C Q.cutoff
  error := E

theorem field_regular
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source) :
    N04bFieldRegularity D S C (Q.field E) base ε :=
  hN.n04b_opticalFieldRegularity hR hS hT
    Q.cutoff Q.cutoff_smooth Q.range_on_component Q.tsupport_interior Q.endpoint_germs
    (fun z hz hs m r hr θ => (Q.corrected_speeds z hz hs m r hr θ).1)
    (Q.field E) rfl
    (fun m r hr θ => hN.n04b_returnCorrectedMinusFlow_reference hS hT Q.cutoff m hr θ)

theorem field_n03
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source)
    (hE : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ ρ η p,
      physicalSourceDecode S (E z ρ η) p =
        returnCorrectionResidualErrorField D S C R Q.cutoff z ρ η p)
    (htame : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (heightPairGrading S))
      S.sourceGrading ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × HeightPair S =>
        E (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    N03Properties D T S C R (Q.field E) base ε := by
  refine ⟨?_, ?_, ?_, ?_, Q.corrected_flow hN hS hT, ?_, ?_, htame,
    (Q.field_regular hN hR hS hT E).toReturnCorrectionSpatialProperties⟩
  · intro z hz hs p
    rfl
  · intro z hz hs p hp hpositive
    exact returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero D S C Q.cutoff z p
      (hN.cutoffs_deriv_eventually_zero_of_nonnegative Q.cutoff
        Q.support_interior Q.endpoint_germs hp.1 hpositive.le)
  · intro z hz hs p hp hzero
    exact returnCorrectedCoefficients_eventuallyEq_of_deriv_eventually_zero D S C Q.cutoff z p
      (hN.cutoffs_deriv_eventually_zero_of_nonnegative Q.cutoff
        Q.support_interior Q.endpoint_germs hp.1 (by rw [hzero]))
  · intro z hz hs r θ
    exact returnCorrectedCoefficients_parity D S C Q.cutoff z
      (fun s t => (originalCoefficients_parity_of_physical hS C z s t).1)
      (fun s t => (originalCoefficients_parity_of_physical hS C z s t).2.1)
      (fun s t => (originalCoefficients_parity_of_physical hS C z s t).2.2) r θ
  · intro z hz hs η p hp
    exact (hN.divergenceOperator_returnCorrectedCoefficients hR hS hT hz hs
      Q.cutoff Q.cutoff_smooth Q.range_on_component Q.support_interior Q.endpoint_germs
      (Q.discriminant_on_support z hz) η p hp).trans
        (hE z hz hs (R.residual z) η p).symm
  · intro z hz hs ρ η
    exact physicalSourceIntegral_decode_source_eq_zero hS (E z ρ η)

end N04bOpticalCutoffData

end ContinuousFlexibility.Statements
