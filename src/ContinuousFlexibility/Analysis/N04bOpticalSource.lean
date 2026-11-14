module

public import ContinuousFlexibility.Analysis.N04bLiteralField
public import ContinuousFlexibility.Analysis.N03SourceFromActualCoefficientJets

/-!
# The actual coefficient family and its literal physical correction

This specializes the upstream source theorem to the retained optical
cutoff data. The family is exactly the actual scalar coefficient jets
restricted to the smooth coefficient space. Its sole quantitative input
is stated for that same family; every qualitative premise is already
proved from the selected cutoff and the original N01 field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n04bOpticalSourceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

namespace N04bOpticalCutoffData

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)

def coefficientJets
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S) :
    MultilinearMap ℝ (fun _ : Fin n => (StateDirections S × ℝ) × CircleSpace S)
      (annularSmoothCoefficientSpace D) :=
  hN.returnCorrectionSmoothCoefficientJets hS hT hR
    Q.cell Q.component_cell Q.cutoff Q.range_on_component Q.derivative_bounds
    Q.active_discriminant Q.cutoff_smooth Q.support_interior Q.endpoint_germs
    Q.stripLeft Q.stripRight Q.stripLeft_gt Q.stripRight_lt Q.strip_support
    (Q.strip_discriminant hN hS hT) n x

theorem coefficientJets_apply
    (n : ℕ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ)
    (v : Fin n → (StateDirections S × ℝ) × CircleSpace S) :
    (Q.coefficientJets hN hS hT hR n x v).val =
      hN.returnCorrectionCoefficientScalarJets hS hT hR
        Q.cell Q.component_cell Q.cutoff Q.range_on_component Q.derivative_bounds
        Q.active_discriminant n x v :=
  hN.returnCorrectionSmoothCoefficientJets_apply hS hT hR
    Q.cell Q.component_cell Q.cutoff Q.range_on_component Q.derivative_bounds
    Q.active_discriminant Q.cutoff_smooth Q.support_interior Q.endpoint_germs
    Q.stripLeft Q.stripRight Q.stripLeft_gt Q.stripRight_lt Q.strip_support
    (Q.strip_discriminant hN hS hT) n x hx v

theorem exists_field_of_coefficient_bounds
    (hcoeff : LocalCoefficientMaterialTameBounds (T := T)
      (U := sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S)))
      (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading)
      (Q.coefficientJets hN hS hT hR)) :
    ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
      N03Properties D T S C R (Q.field E) base ε ∧
      N04bFieldRegularity D S C (Q.field E) base ε := by
  obtain ⟨E, hE, htame⟩ :=
    hN.exists_returnCorrectionSource_of_actual_coefficient_bounds hS hT hR
      Q.cell Q.component_cell Q.cutoff Q.range_on_component Q.derivative_bounds
      Q.active_discriminant Q.cutoff_smooth Q.support_interior Q.endpoint_germs
      Q.stripLeft Q.stripRight Q.stripLeft_gt Q.stripRight_lt Q.strip_support
      (Q.strip_discriminant hN hS hT) Q.discriminant_on_support hcoeff
  exact ⟨E, Q.field_n03 hN hR hS hT E hE htame, Q.field_regular hN hR hS hT E⟩

end N04bOpticalCutoffData

end ContinuousFlexibility.Statements
