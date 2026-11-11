import ContinuousFlexibility.Analysis.N01EndpointSmoothTame
import ContinuousFlexibility.Analysis.N01FlowSmallness
import ContinuousFlexibility.Analysis.CirclePositiveInverseSmoothTame
import ContinuousFlexibility.Analysis.CirclePositiveInversePerturbation
import ContinuousFlexibility.Analysis.CircleJointEvaluation

/-!
# Actual inverse flows at every fixed selector of closed radii

The realized forward displacement has precisely the original N01 flow
as its affine lift. Its positive-lift inverse is therefore the original
fiberwise invFun. Inverse composition supplies the inverse displacement
inside the given circle space, with a complete smooth tame tower on the
original sector neighborhood. No inverse membership or parameter
regularity is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01SelectorInverseStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem sectorPairGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (pairGrading (sectorGrading S) realGrading) := by
  have hr : WithSeminorms realGrading := by
    apply (norm_withSeminorms ℝ ℝ).congr
    · intro n
      exact ⟨{()}, 1, by simp [realGrading]⟩
    · intro u
      exact ⟨{0}, 1, by simp [realGrading]⟩
  exact withSeminorms_pairGrading (solve_sectorGrading_withSeminorms S) hr

theorem N01Properties.endpointFlowCircle_affineLift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    circleAffineLift (fun m => -opticalTravel D.w (C.left m) (rsel m))
      ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z)) 1 =
        fun m => C.minusFlow (liftSectorParameter S C z) m (rsel m) := by
  funext m θ
  unfold circleAffineLift
  rw [hN.endpointFlowCircle_decode_apply hS hT rsel hrsel z hz m θ,
    hN.minusFlow_reference_eq hS hT m (hrsel m) θ]
  ring

theorem N01Properties.endpointFlowCircle_mem_positiveLiftDomain
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.endpointFlowCircle hS hT rsel hrsel z ∈
      circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ))
    (fun m => -opticalTravel D.w (C.left m) (rsel m)) _).mpr
  rw [hN.endpointFlowCircle_affineLift hS hT rsel hrsel z hz]
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hmem := liftSectorParameter_mem_stateNeighborhood hz (le_refl ε)
  exact fun m θ => ((hflow _ hmem m θ).2.2.2 (rsel m) (hrsel m)).1

theorem N01Properties.endpointFlowCircle_affineInverse
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    circleAffineInverse (fun m => -opticalTravel D.w (C.left m) (rsel m))
      (hN.endpointFlowCircle hS hT rsel hrsel z) =
        fun m => Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) := by
  funext m
  change Function.invFun
      (circleAffineLift (fun j => -opticalTravel D.w (C.left j) (rsel j))
        ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z)) 1 m) = _
  exact congrArg (fun f : ℝ → ℝ => Function.invFun f)
    (congrFun (hN.endpointFlowCircle_affineLift hS hT rsel hrsel z hz) m)

/-- The actual inverse displacement, realized through the existing
circle decoder. The reference inverse is the opposite optical translation. -/
def N01Properties.selectorInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun m => -opticalTravel D.w (C.left m) (rsel m))
    (hN.endpointFlowCircle hS hT rsel hrsel z)

theorem N01Properties.selectorInverseCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    (S.circle (3 / 4 : ℝ)).decode (hN.selectorInverseCircle hS hT rsel hrsel z) =
      fun m θ => Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ -
        (θ + opticalTravel D.w (C.left m) (rsel m)) := by
  have hd := circlePositiveInversePerturbation_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun m => -opticalTravel D.w (C.left m) (rsel m))
    (hN.endpointFlowCircle hS hT rsel hrsel z)
    (hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel z hz)
  refine hd.trans ?_
  funext m θ
  rw [hN.endpointFlowCircle_affineInverse hS hT rsel hrsel z hz]
  simp only [sub_neg_eq_add]

theorem N01Properties.smoothTameOn_selectorInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.selectorInverseCircle hS hT rsel hrsel) := by
  let B := S.circle (3 / 4 : ℝ)
  let travel : ℕ → ℝ := fun m => -opticalTravel D.w (C.left m) (rsel m)
  have hB : IsCircleModel T (3 / 4 : ℝ) B := hS.2.1 (3 / 4 : ℝ)
  have hinterp : HasInterpolation B.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  letI : ∀ n, CompleteSpace (B.level n) :=
    fun n => (hB.2.1 n).isComplete.completeSpace_coe
  have hneg := smoothTameOn_circlePositiveInversePerturbation hB hT hN.1.1
    (by norm_num) hinterp travel
  have hmap : MapsTo (hN.endpointFlowCircle hS hT rsel hrsel)
      (sectorNeighborhood S base ε ε) (circlePositiveLiftDomain B) :=
    fun z hz => hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel z hz
  exact smoothTameOn_comp_topological
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (withSeminorms_graded (fun n => B.level n) B.bond)
    (sectorNeighborhood_isOpen S base ε ε)
    (circlePositiveLiftDomain_isOpen hB hT hN.1.1 (by norm_num)) hmap
    (hN.smoothTameOn_endpointFlowCircle hS hT rsel hrsel) hneg

/-- The actual inverse flow with both its sector parameter and its angle
variable. Its source topology is the original projective sector topology. -/
def N01Properties.selectorInverse_jointTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (m : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        Function.invFun (C.minusFlow (liftSectorParameter S C p.1) m (rsel m)) p.2) := by
  let J := (hN.smoothTameOn_selectorInverseCircle hS hT rsel hrsel).choose
  have hH (j : ℕ) : 0 < T.H (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j)).2.1
  let K := circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m
  let L : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ
  let R := (smoothDirectionsLinear (ContinuousLinearMap.id ℝ ℝ)).compAffine L
    (opticalTravel D.w (C.left m) (rsel m))
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    (fun _ _ => mem_univ _)
  apply (smoothDirectionsAdd K R).congrOn
  intro p hp
  change (S.circle (3 / 4 : ℝ)).decode (hN.selectorInverseCircle hS hT rsel hrsel p.1) m p.2 +
    (opticalTravel D.w (C.left m) (rsel m) + p.2) = _
  rw [hN.selectorInverseCircle_decode hS hT rsel hrsel p.1 hp.1]
  ring

end ContinuousFlexibility.Statements
