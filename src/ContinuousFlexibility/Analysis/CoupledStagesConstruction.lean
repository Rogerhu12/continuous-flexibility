import ContinuousFlexibility.Analysis.CoupledN09Construction
import ContinuousFlexibility.Analysis.CoupledN10Construction

/-!
# Passing from the N08 data to the complete nonlinear construction

The two circle calculus inputs are properties of the actual N02 chart and
error. The control and coefficient estimates choose one common smaller
neighborhood, while all data and the recovered inverse are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b : ℕ} {Domain : CanonicalDomainData S K Vol b}
  {Relative : RelativeInverseData S K Vol b Domain}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

theorem coupled_nonlinearStagesThrough10_of_circle_calculus
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h08 : NonlinearPropertiesThrough08 D T S C R L K Vol b Domain Relative G P B
      base loss ε)
    (hchart : SmoothTameOn
      (pairGrading (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × CircleSpace S =>
        R.chartIncrement (liftSectorParameter S C z.1) z.2))
    (hRerror : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    ∃ base' : ℕ, ∃ ε' q0 : ℝ, NonlinearStagesThrough10 D T S C R base' loss ε' q0 := by
  have h1 : N01Properties D T S C base loss ε := h08.1.1.1.1.1.1.1
  have h2 : N02Properties D T S C R base ε := h08.1.1.1.1.1.1.2
  have hG : ScalarInverseProperties D S C L G base ε := h08.1.2.1
  have hN := coupled_exists_N09Properties hT hS h1 h2 hG h08.2 hchart
  let base1 : ℕ := hN.choose
  let ε1 : ℝ := hN.choose_spec.choose
  let q1 : ℝ := hN.choose_spec.choose_spec.choose
  have hs := hN.choose_spec.choose_spec.choose_spec
  have h08' := coupled_nonlinearPropertiesThrough08_restrict
    hT h08 hs.1 hs.2.2.1 hs.2.1
  have h09 : NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G P B
      (coupledControlInverse S B G) (coupledRecoveredInverseData hT hS h1 h2 h08.2)
      base1 loss ε1 q1 := ⟨h08', hs.2.2.2⟩
  have hU : IsOpen (sectorNeighborhood S base1 ε1 ε1) :=
    coupled_sectorNeighborhood_isOpen S base1 ε1 ε1
  have hsub : sectorNeighborhood S base1 ε1 ε1 ⊆ sectorNeighborhood S base ε ε :=
    coupled_sectorNeighborhood_mono hs.1 hs.2.2.1 hs.2.2.1
  have hRerror' := smoothTameOn_mono hRerror ((hU.prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono (Set.prod_mono hsub (subset_refl _)) (subset_refl _))
  exact coupled_nonlinearStagesThrough10_of_returnErrorSmooth hT hS h09 hRerror'

end ContinuousFlexibility.Statements
