import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsInverseComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsEvaluation
import ContinuousFlexibility.Analysis.N04EndpointCircleFixedBaseBounds
import ContinuousFlexibility.Analysis.N01ReturnInverseCircle
import ContinuousFlexibility.Analysis.N01RootLabels
import ContinuousFlexibility.Analysis.SolveStateSpaces

/-!
# Fixed-base bounds for the actual right-root inverse circle

The original return transport is inverse composition of the actual
closed-radius flow with the chart-minus-flow displacement. Its odd part
is exactly the original right-root label. A second genuine positive
inverse therefore gives the stored right-root inverse circle. Every
stage retains one low parameter order before all derivative orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04PositiveEndpointBoundsRightStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem endpointParameter_affineInterpolation
    (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading realGrading
      (pairGrading (sectorGrading S) realGrading)) :=
  hasInterpolation_of_hasSmoothing
    (tamePairGrading_monotone (fun _ _ _ _ => le_rfl) (sectorPairGrading_monotone S))
    (hasSmoothing_pairGrading hasSmoothing_realGrading
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading))

private theorem returnFlow_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    1 / 2 ≤ 1 + deriv ((S.circle (3 / 4 : ℝ)).decode
      (hN.returnFlowCircle hS hT x) m) θ := by
  rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ)) (fun j => -C.travel j),
    hN.returnFlowCircle_lift hS hT x hx m]
  exact (hflow (liftSectorParameter S C x)
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    m (C.right m) (hN.right_radius_mem m) θ).1

/-- Fixed-base bounds for the unchanged actual return transport circle. -/
theorem n04PositiveGeometry_returnTransportCircle_fixedBaseBounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (Jout : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.sectorReturnTransportCircle hS hT)) :
    N04EndpointFixedBaseBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading Jout := by
  let p := pairGrading (sectorGrading S) realGrading
  let H := S.circle (3 / 4 : ℝ)
  let U := sectorNeighborhood S base ε ε
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hp : Monotone p := sectorPairGrading_monotone S
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  let JF : SmoothDirections U (hN.returnFlowCircle hS hT) :=
    (hN.exists_endpointFlowCircle_smoothDirections hS hT C.right hN.right_radius_mem).choose
  have hF : N04EndpointFixedBaseBounds p H.grading JF := by
    refine (hN.endpointFlowCircle_fixedBase_oneHigh hS hT).elim ?_
    intro B hB
    refine ⟨B, fun n => ?_⟩
    refine (hB.2 n).elim ?_
    intro ell hell
    exact ⟨ell, fun R hR s => (hell R hR s).elim
      (fun K hK => ⟨K, hK.1, hK.2 C.right hN.right_radius_mem JF⟩)⟩
  let JC := smoothDirectionsLinearOn (sectorChartContinuousLinear S) hU
  have hC : N04EndpointFixedBaseBounds p H.grading JC :=
    n04PositiveGeometry_endpointBounds_linear p H.grading
      (sectorChartContinuousLinear S) hU (fun s => ⟨1, zero_le_one, fun x => by
        simpa only [one_mul, sectorChartContinuousLinear_apply] using
          sectorParameter_chart_grading_le S s x⟩)
  let Lsub : (H.Space × H.Space) →L[ℝ] H.Space :=
    ContinuousLinearMap.snd ℝ H.Space H.Space - ContinuousLinearMap.fst ℝ H.Space H.Space
  have hLsub (s : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ y,
      H.grading s (Lsub y) ≤ A * pairGrading H.grading H.grading (s + 0) y := by
    refine ⟨1, zero_le_one, fun y => ?_⟩
    simpa only [Lsub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', pairGrading_apply, Nat.add_zero, one_mul, add_comm] using
        (map_sub_le_add (H.grading s) y.2 y.1)
  let JD := solveSmoothDirectionsPostcomp (smoothDirectionsProd JF JC) Lsub
  have hD : N04EndpointFixedBaseBounds p H.grading JD := (hF.prod hp hC).postLinear Lsub 0 hLsub
  exact n04PositiveGeometry_endpointBounds_inverseCompose hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp (endpointParameter_affineInterpolation hS)
    hF hD (fun m => -C.travel m) (by norm_num : (0 : ℝ) < 1 / 2)
    (fun _ hx => returnFlow_lower hT hS hN hflow hx) Jout

/-- The stored right inverse circle has the fixed-base estimate after
the actual ordinary-flow Jacobian has been made uniformly positive. -/
theorem n04PositiveGeometry_rightRootInverseCircle_fixedBaseBounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (Jout : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.rightChartInverseCircle hS hT)) :
    N04EndpointFixedBaseBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading Jout := by
  let p := pairGrading (sectorGrading S) realGrading
  let H := S.circle (3 / 4 : ℝ)
  let U := sectorNeighborhood S base ε ε
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hp : Monotone p := sectorPairGrading_monotone S
  let JT := (hN.smoothTameOn_sectorReturnTransportCircle hS hT).choose
  have hJT := n04PositiveGeometry_returnTransportCircle_fixedBaseBounds hT hS hN hflow JT
  let JO := solveSmoothDirectionsPostcomp JT (circleOddContinuousLinear hH)
  have hJO : N04EndpointFixedBaseBounds p H.grading JO := by
    apply hJT.postLinear (circleOddContinuousLinear hH) 0
    intro s
    refine (circleOddLinear_tame hH s (Nat.zero_le s)).elim ?_
    intro A hA
    exact ⟨A, A.coe_nonneg, fun y => hA y⟩
  let Lneg : H.Space →L[ℝ] H.Space := -ContinuousLinearMap.id ℝ H.Space
  let Jneg := solveSmoothDirectionsPostcomp JO Lneg
  have hJneg : N04EndpointFixedBaseBounds p H.grading Jneg := by
    apply hJO.postLinear Lneg 0
    intro s
    refine ⟨1, zero_le_one, fun y => ?_⟩
    simp only [Lneg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      map_neg_eq_map, Nat.add_zero, one_mul]
  have hlower : ∀ x ∈ U, ∀ m θ,
      1 / 4 ≤ 1 + deriv (H.decode
        (circleOddContinuousLinear hH (hN.sectorReturnTransportCircle hS hT x)) m) θ := by
    intro x hx m θ
    have hlift := hN.sectorReturnTransportCircle_odd_lift hS hT x hx m
    have hd := congrArg (fun f : ℝ → ℝ => deriv f θ) hlift
    have hb := (n01RootLabel_deriv_bounds hN hflow
      (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x) m true θ).1
    have hraw : 1 / 4 ≤ deriv (circleAffineLift (fun _ => 0)
        (H.decode (circleOddLinear hH (hN.sectorReturnTransportCircle hS hT x))) 1 m) θ :=
      hb.trans_eq hd.symm
    simpa only [circleAffineLift_deriv hH, circleOddContinuousLinear_apply] using hraw
  let JQ : SmoothDirections U (fun x =>
      circlePositiveInverseComposeLinear hH hT hN.1.1 (by norm_num) (fun _ => 0)
        (circleOddContinuousLinear hH (hN.sectorReturnTransportCircle hS hT x))
        (Lneg (circleOddContinuousLinear hH (hN.sectorReturnTransportCircle hS hT x)))) :=
    Jout.congrOn (fun x _ =>
      ((circlePositiveInverseComposeLinear hH hT hN.1.1 (by norm_num) (fun _ => 0)
        (circleOddLinear hH (hN.sectorReturnTransportCircle hS hT x))).map_neg
          (circleOddLinear hH (hN.sectorReturnTransportCircle hS hT x))).symm)
  exact n04PositiveGeometry_endpointBounds_inverseCompose hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 hp (endpointParameter_affineInterpolation hS)
    hJO hJneg (fun _ => 0) (by norm_num : (0 : ℝ) < 1 / 4) hlower JQ

end ContinuousFlexibility.Analysis
