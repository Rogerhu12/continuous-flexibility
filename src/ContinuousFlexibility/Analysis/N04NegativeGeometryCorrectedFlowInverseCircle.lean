import ContinuousFlexibility.Analysis.N04NegativeGeometryCorrectedFlowCircle

/-!
# The inverse of the same corrected flow

The actual positive angular derivatives put the corrected circle lift
in the existing inverse operator's domain. Its decoder is then exactly
the inverse of the original corrected flow, with the opposite optical
translation. The resulting state-and-angle derivatives are genuine.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance n04NegativeGeometryCorrectedFlowInverseCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.n04NegativeGeometryCorrectedFlowCircle_mem_positiveLiftDomain
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z ∈
      circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ))
    (fun m => -opticalTravel D.w (C.left m) (rsel m)) _).mpr
  rw [hN.n04NegativeGeometryCorrectedFlowCircle_affineLift hS hT χ hχrange rsel hrsel z hz]
  intro m θ
  let initial : ℝ → ℝ := returnInterpolation (χ m (rsel m))
    (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)
  let flow : ℝ → ℝ := C.minusFlow (liftSectorParameter S C z) m (rsel m)
  have hi : 0 < deriv initial θ := by
    have h := (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mp
      (hN.interpolationSelectorCircle_positive hS hT χ hχrange rsel hrsel z hz) m θ
    rw [hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m] at h
    exact h
  have hf : 0 < deriv flow (initial θ) := by
    have h := (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ))
      (fun j => -opticalTravel D.w (C.left j) (rsel j)) _).mp
      (hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel z hz) m (initial θ)
    rw [hN.endpointFlowCircle_affineLift hS hT rsel hrsel z hz] at h
    exact h
  have hc : HasDerivAt (fun t => flow (initial t))
      (deriv flow (initial θ) * deriv initial θ) θ :=
    (differentiableAt_of_deriv_ne_zero hf.ne').hasDerivAt.comp θ
      (differentiableAt_of_deriv_ne_zero hi.ne').hasDerivAt
  change 0 < deriv (fun t => flow (initial t)) θ
  rw [hc.deriv]
  exact mul_pos hf hi

theorem N01Properties.n04NegativeGeometryCorrectedFlowCircle_affineInverse
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    circleAffineInverse (fun m => -opticalTravel D.w (C.left m) (rsel m))
      (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z) =
      fun m => Function.invFun
        (returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m (rsel m)) := by
  funext m
  change Function.invFun
      (circleAffineLift (fun j => -opticalTravel D.w (C.left j) (rsel j))
        ((S.circle (3 / 4 : ℝ)).decode
          (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z)) 1 m) = _
  exact congrArg (fun f : ℝ → ℝ => Function.invFun f)
    (congrFun (hN.n04NegativeGeometryCorrectedFlowCircle_affineLift hS hT χ hχrange rsel hrsel z hz) m)

def N01Properties.n04NegativeGeometryCorrectedFlowInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun m => -opticalTravel D.w (C.left m) (rsel m))
    (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z)

theorem N01Properties.n04NegativeGeometryCorrectedFlowInverseCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    (S.circle (3 / 4 : ℝ)).decode
      (hN.n04NegativeGeometryCorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel z) =
      fun m θ => Function.invFun
        (returnCorrectedMinusFlow S C χ (liftSectorParameter S C z) m (rsel m)) θ -
          (θ + opticalTravel D.w (C.left m) (rsel m)) := by
  have hd := circlePositiveInversePerturbation_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun m => -opticalTravel D.w (C.left m) (rsel m))
    (hN.n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel z)
    (hN.n04NegativeGeometryCorrectedFlowCircle_mem_positiveLiftDomain hS hT χ hχrange rsel hrsel z hz)
  refine hd.trans ?_
  funext m θ
  rw [hN.n04NegativeGeometryCorrectedFlowCircle_affineInverse hS hT χ hχrange rsel hrsel z hz]
  simp only [sub_neg_eq_add]

theorem N01Properties.smoothTameOn_n04NegativeGeometryCorrectedFlowInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.n04NegativeGeometryCorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact smoothTameOn_comp_topological
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => H.level n) H.bond)
    (sectorNeighborhood_isOpen S base ε ε)
    (circlePositiveLiftDomain_isOpen hH hT hN.1.1 (by norm_num))
    (fun z hz => hN.n04NegativeGeometryCorrectedFlowCircle_mem_positiveLiftDomain
      hS hT χ hχrange rsel hrsel z hz)
    (hN.smoothTameOn_n04NegativeGeometryCorrectedFlowCircle hS hT χ hχrange rsel hrsel)
    (smoothTameOn_circlePositiveInversePerturbation hH hT hN.1.1 (by norm_num)
      (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
      (fun m => -opticalTravel D.w (C.left m) (rsel m)))

def N01Properties.n04NegativeGeometryCorrectedFlowInverseSelector_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ => Function.invFun
        (returnCorrectedMinusFlow S C χ (liftSectorParameter S C p.1) m (rsel m)) p.2) := by
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.n04NegativeGeometryCorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel) :=
    (hN.smoothTameOn_n04NegativeGeometryCorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel).choose
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  let travel : ℕ → ℝ := fun j => opticalTravel D.w (C.left j) (rsel j)
  let K := circleAffineLiftJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J travel m
  apply K.congrOn
  intro p hp
  let a : ℝ := p.2 + travel m
  let b : ℝ := Function.invFun
    (returnCorrectedMinusFlow S C χ (liftSectorParameter S C p.1) m (rsel m)) p.2
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (hN.n04NegativeGeometryCorrectedFlowInverseCircle hS hT χ hχrange rsel hrsel p.1) m p.2 = b - a :=
    congrArg (fun u : ℕ → ℝ → ℝ => u m p.2)
      (hN.n04NegativeGeometryCorrectedFlowInverseCircle_decode hS hT χ hχrange rsel hrsel p.1 hp.1)
  exact (congrArg (fun y : ℝ => a + y) hd).trans
    ((add_comm a (b - a)).trans (sub_add_cancel b a))

end ContinuousFlexibility.Statements
