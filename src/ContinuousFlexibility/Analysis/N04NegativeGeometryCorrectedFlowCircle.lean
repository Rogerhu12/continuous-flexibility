import ContinuousFlexibility.Analysis.N01InterpolationInverseCircle
import ContinuousFlexibility.Analysis.ReturnCorrectedFlow

/-!
# The actual corrected flow as one circle-valued family

The same initial interpolation and original flow are composed in the
given circle model. Their affine lift is the literal corrected flow,
so the genuine circle tower also supplies its state-and-angle tower.
The radius selector is arbitrary but fixed in this construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04NegativeGeometryCorrectedFlowCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def N01Properties.n04NegativeGeometryCorrectedFlowCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z +
    circleShiftedChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z)
      (hN.endpointFlowCircle hS hT rsel hrsel z)

theorem N01Properties.n04NegativeGeometryCorrectedFlowCircle_affineLift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    circleAffineLift (fun m => -opticalTravel D.w (C.left m) (rsel m))
      ((S.circle (3 / 4 : ℝ)).decode
        (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z)) 1 =
      fun m => returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m (rsel m) := by
  funext m θ
  let e : CircleSpace S := hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z
  let f : CircleSpace S := hN.endpointFlowCircle hS hT rsel hrsel z
  let de : ℝ := (S.circle (3 / 4 : ℝ)).decode e m θ
  have hinterp : θ + de = returnInterpolation (χ m (rsel m))
      (returnCorrectionInitialMap S C (liftSectorParameter S C z) m) θ := by
    simpa only [circleAffineLift, add_zero, one_mul] using
      congrFun (hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m) θ
  have hflow : (θ + de) + -opticalTravel D.w (C.left m) (rsel m) +
      (S.circle (3 / 4 : ℝ)).decode f m (θ + de) =
      C.minusFlow (liftSectorParameter S C z) m (rsel m) (θ + de) := by
    simpa only [circleAffineLift, one_mul] using congrFun
      (congrFun (hN.endpointFlowCircle_affineLift hS hT rsel hrsel z hz) m) (θ + de)
  have hdecode : (S.circle (3 / 4 : ℝ)).decode
      (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z) m θ =
      de + (S.circle (3 / 4 : ℝ)).decode f m (θ + de) := by
    simp only [n04NegativeGeometryCorrectedFlowCircle, map_add, Pi.add_apply,
      circleShiftedChartComposeLinear_decode, add_zero, e, f, de]
  change θ + -opticalTravel D.w (C.left m) (rsel m) +
      1 * (S.circle (3 / 4 : ℝ)).decode
        (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z) m θ = _
  rw [one_mul, hdecode]
  calc
    _ = (θ + de) + -opticalTravel D.w (C.left m) (rsel m) +
        (S.circle (3 / 4 : ℝ)).decode f m (θ + de) := by ring
    _ = C.minusFlow (liftSectorParameter S C z) m (rsel m) (θ + de) := hflow
    _ = returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m (rsel m) θ := by
      rw [returnCorrectedMinusFlow_apply, hinterp]

theorem N01Properties.smoothTameOn_n04NegativeGeometryCorrectedFlowCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel) := by
  have he := hN.smoothTameOn_interpolationSelectorCircle hS hT χ hχrange rsel hrsel
  have hf := hN.smoothTameOn_endpointFlowCircle hS hT rsel hrsel
  have hcomp := smoothTameOn_circleShiftedChartCompose_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0)
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (sectorNeighborhood_isOpen S base ε ε) he hf
  unfold n04NegativeGeometryCorrectedFlowCircle
  exact smoothTameOn_add (sectorPairGrading_monotone S) he hcomp

def N01Properties.n04NegativeGeometryCorrectedFlowSelector_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        returnCorrectedMinusFlow S C χ (liftSectorParameter S C p.1) m (rsel m) p.2) := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel) :=
    (hN.smoothTameOn_n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel).choose
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  let K := circleAffineLiftJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J
    (fun j => -opticalTravel D.w (C.left j) (rsel j)) m
  apply K.congrOn
  intro p hp
  simpa only [circleAffineLift, one_mul] using congrFun
    (congrFun (hN.n04NegativeGeometryCorrectedFlowCircle_affineLift
      hS hT χ hχrange rsel hrsel p.1 hp.1) m) p.2

end ContinuousFlexibility.Statements
