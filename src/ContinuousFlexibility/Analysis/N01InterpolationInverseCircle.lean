import ContinuousFlexibility.Analysis.N01ReturnInverseCircle
import ContinuousFlexibility.Analysis.CircleComponentContraction

/-!
# The same cutoff interpolation and its actual inverse in the circle model

At any selector of closed radii, the supplied cutoff acts by a
componentwise contraction on the already constructed initial correction.
The resulting affine lift is exactly the interpolation used by the
corrected flow. Its inverse displacement and its joint parameter-angle
tower are obtained on the original N01 sector neighborhood.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01InterpolationInverseCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem cutoffSelector_abs_le_one
    (χ : ℕ → ℝ → ℝ) (rsel : ℕ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    |χ m (rsel m)| ≤ 1 := by
  have h := hχrange m (rsel m) (hrsel m)
  simpa only [abs_of_nonneg h.1] using h.2

def N01Properties.interpolationSelectorCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circleComponentContractionLinear (hS.2.1 (3 / 4 : ℝ))
    (fun m => χ m (rsel m)) (cutoffSelector_abs_le_one χ rsel hχrange hrsel)
    (hN.returnCorrectionInitialCircle hS hT z)

theorem N01Properties.interpolationSelectorCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) m θ =
      χ m (rsel m) * (returnCorrectionInitialMap S C (liftSectorParameter S C z) m θ - θ) := by
  unfold N01Properties.interpolationSelectorCircle
  rw [circleComponentContractionLinear_decode,
    hN.returnCorrectionInitialCircle_decode hS hT z hz m θ]

theorem N01Properties.interpolationSelectorCircle_lift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    circleAffineLift (fun _ => 0)
      ((S.circle (3 / 4 : ℝ)).decode
        (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z)) 1 m =
      returnInterpolation (χ m (rsel m))
        (returnCorrectionInitialMap S C (liftSectorParameter S C z) m) := by
  funext θ
  simp only [circleAffineLift, add_zero, one_mul,
    hN.interpolationSelectorCircle_decode hS hT χ hχrange rsel hrsel z hz m θ,
    returnInterpolation_apply]

theorem N01Properties.interpolationSelectorCircle_positive
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z ∈
      circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mpr
  intro m θ
  rw [hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m]
  have hk := hN.returnCorrectionInitialMap_deriv_pos
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z) m θ
  have hd := (differentiableAt_of_deriv_ne_zero hk.ne').hasDerivAt
  rw [(returnInterpolation_hasDerivAt (χ := χ m (rsel m)) hd).deriv]
  exact returnInterpolation_deriv_pos (hχrange m (rsel m) (hrsel m)).1
    (hχrange m (rsel m) (hrsel m)).2 hk

theorem N01Properties.smoothTameOn_interpolationSelectorCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact smoothTameOn_comp_topological
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => H.level n) H.bond)
    (sectorNeighborhood_isOpen S base ε ε) isOpen_univ (fun _ _ => mem_univ _)
    (hN.smoothTameOn_returnCorrectionInitialCircle hS hT)
    (smoothTameOn_circleComponentContractionLinear hH (fun m => χ m (rsel m))
      (cutoffSelector_abs_le_one χ rsel hχrange hrsel))

def N01Properties.interpolationInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z)

theorem N01Properties.interpolationInverseCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.interpolationInverseCircle hS hT χ hχrange rsel hrsel z) m θ =
      Function.invFun (returnInterpolation (χ m (rsel m))
        (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) θ - θ := by
  have hd := congrFun (congrFun (circlePositiveInversePerturbation_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
    (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z)
    (hN.interpolationSelectorCircle_positive hS hT χ hχrange rsel hrsel z hz)) m) θ
  have hinv : circleAffineInverse (fun _ => 0)
      (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) m θ =
      Function.invFun (returnInterpolation (χ m (rsel m))
        (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
      (hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m)
  exact hd.trans (by rw [hinv, sub_zero])

theorem N01Properties.smoothTameOn_interpolationInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.interpolationInverseCircle hS hT χ hχrange rsel hrsel) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact smoothTameOn_comp_topological
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => H.level n) H.bond)
    (sectorNeighborhood_isOpen S base ε ε)
    (circlePositiveLiftDomain_isOpen hH hT hN.1.1 (by norm_num))
    (fun z hz => hN.interpolationSelectorCircle_positive hS hT χ hχrange rsel hrsel z hz)
    (hN.smoothTameOn_interpolationSelectorCircle hS hT χ hχrange rsel hrsel)
    (smoothTameOn_circlePositiveInversePerturbation hH hT hN.1.1 (by norm_num)
      (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0))

def N01Properties.interpolationInverse_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        Function.invFun (returnInterpolation (χ m (rsel m))
          (returnCorrectionInitialMap S C (liftSectorParameter S C p.1) m)) p.2) := by
  let J := (hN.smoothTameOn_interpolationInverseCircle hS hT χ hχrange rsel hrsel).choose
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  apply (circleAffineLiftJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J (fun _ => 0) m).congrOn
  intro p hp
  rw [hN.interpolationInverseCircle_decode hS hT χ hχrange rsel hrsel p.1 hp.1 m p.2]
  ring

end ContinuousFlexibility.Statements
