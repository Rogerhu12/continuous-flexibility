import ContinuousFlexibility.Analysis.N04bOpticalSource
import ContinuousFlexibility.Analysis.N01CorrectionCoefficientMaterialTame

/-!
# The actual buffered optical field, including its source estimate

The selected cutoff already supplies every geometric and quantitative
input for the actual coefficient estimate. The same coefficient jets
therefore produce the bilinear source, and the literal corrected field
retains all N03 identities and all five raw field properties.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n04bOpticalFieldRealizationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

namespace N04bOpticalCutoffData

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)

/-- The genuine material estimate for the already fixed coefficient family. -/
theorem coefficientJets_local_bounds :
    LocalCoefficientMaterialTameBounds (T := T)
      (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading)
      (Q.coefficientJets hN hS hT hR) :=
  hN.returnCorrectionSmoothCoefficientJets_local_material_tame hS hT hR
    Q.cell Q.component_cell Q.cutoff Q.range_on_component Q.derivative_bounds
    Q.active_discriminant Q.cutoff_smooth Q.support_interior Q.endpoint_germs
    Q.stripLeft Q.stripRight Q.stripLeft_gt Q.stripRight_lt Q.strip_support
    (Q.strip_discriminant hN hS hT) (Q.sector_flow_slope hN)
    Q.discScale_pos Q.discPower_pos.le Q.strip_positive

/-- One actual source and the same literal coefficient/flow formulas
satisfy the complete physical field contract. -/
include hN hS hT hR in
theorem exists_field :
    ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
      N03Properties D T S C R (Q.field E) base ε ∧
        N04bFieldRegularity D S C (Q.field E) base ε :=
  Q.exists_field_of_coefficient_bounds hN hS hT hR
    (Q.coefficientJets_local_bounds hN hS hT hR)

end N04bOpticalCutoffData

end ContinuousFlexibility.Statements
