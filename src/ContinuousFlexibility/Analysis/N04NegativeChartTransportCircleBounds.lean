module

public import ContinuousFlexibility.Analysis.N04NegativeChartReturnCircleBounds
public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualLinear

/-!
# Fixed-base inputs for the actual interior transport system

The slope uses the derivative of the actual flow followed by its inverse.
For the pulled correction, the supplied N02 residual gives exactly the
already estimated initial displacement. The two actual inverse maps then
give a common low order before all state orders and radius selectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
    r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
      deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)

include hflow in
theorem N01Properties.n04FixedBase_selectorInverseSlopeCircle
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i => hN.selectorInverseSlopeCircle hS hT (rsel i) (hrsel i)) := by
  let hH : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hf := hN.n04FixedBase_endpointFlowCircle hS hT rsel hrsel
  have hd := (hf.postTameContinuousLinear (circleDerivativeContinuousLinear hH)
    (circleDerivativeLinear_isTame hH)).congr
      (fun i z _ => circleDerivativeContinuousLinear_apply hH
        (hN.endpointFlowCircle hS hT (rsel i) (hrsel i) z))
  exact n04FixedBaseSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 2) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) z hz m θ) hf hd

theorem N01Properties.n04NegativeChart_initialCircle_eq_actualDisplacement
    (hR : N02Properties D T S C R base ε)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.returnCorrectionInitialCircle hS hT z =
      hN.returnCorrectionDisplacementCircleLinear hS hT z
        (R.residual (liftSectorParameter S C z)) := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  exact (hN.returnCorrectionInitialCircle_decode hS hT z hz m θ).trans
    ((hN.returnCorrectionDisplacementCircleLinear_decode hS hT z hz
      (R.residual (liftSectorParameter S C z)) m θ).trans
        (returnCorrectionDisplacementLinear_at_actual hN hR
          (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
          (hN.2.2.1.liftSectorParameter_sector z) m θ)).symm

include hflow in
theorem N01Properties.n04FixedBase_actualPulledCorrectionCircle
    (hR : N02Properties D T S C R base ε)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : I → ℕ → ℝ) (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m)) :
    N04FixedBaseSmoothFamilyOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun i z => hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange
        (rsel i) (hrsel i) z (R.residual (liftSectorParameter S C z))) := by
  let hH : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 (3 / 4 : ℝ)
  have hd := (hN.n04FixedBase_returnCorrectionInitialCircle (I := I) hS hT hflow).congr
    (fun _ z hz => hN.n04NegativeChart_initialCircle_eq_actualDisplacement hS hT hR z hz)
  have hi := hN.n04FixedBase_interpolationSelectorCircle hS hT hflow χ hχrange rsel hrsel
  have hfirst := n04FixedBaseSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ : I => fun _ => 0) (1 / 12) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.interpolationSelectorCircle_uniform_lower hS hT hflow
      χ hχrange (rsel i) (hrsel i) z hz m θ) hi hd
  have hf := hN.n04FixedBase_endpointFlowCircle hS hT rsel hrsel
  have hsecond := n04FixedBaseSmoothFamilyOn_circleInverse_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i m => -opticalTravel D.w (C.left m) (rsel i m)) (1 / 2) (by norm_num)
    (sectorPairGrading_monotone S) (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun i z hz m θ => hN.endpointFlowCircle_uniform_lower hS hT hflow
      (rsel i) (hrsel i) z hz m θ) hf hfirst
  exact hsecond.congr (fun _ _ _ => by
    simp only [N01Properties.returnCorrectionPulledDisplacementCircleLinear, LinearMap.comp_apply])

end ContinuousFlexibility.Statements

/-- info: 'ContinuousFlexibility.Statements.N01Properties.n04FixedBase_actualPulledCorrectionCircle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Statements.N01Properties.n04FixedBase_actualPulledCorrectionCircle
