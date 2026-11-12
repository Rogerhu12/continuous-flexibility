import ContinuousFlexibility.Analysis.N01SingleComponentInterpolation

/-!
# The actual cutoff velocity jointly in state, radius and angle

The independent displacement is pulled through the actual interpolation
inverse and the actual flow inverse. The same variable-radius cutoff
then multiplies the exact old-flow slope. All operations take place in
the original circle model; the final decoder is the existing velocity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01ReturnVelocitySpatialTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology

def correctionStateRadiusProjection (S : PhysicalSpacesData) :
    (((StateDirections S × ℝ) × CircleSpace S) × ℝ) →L[ℝ]
      (StateDirections S × ℝ) × ℝ :=
  ((ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) (CircleSpace S)).comp
    (ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × CircleSpace S) ℝ)).prod
      (ContinuousLinearMap.snd ℝ ((StateDirections S × ℝ) × CircleSpace S) ℝ)

def parameterSpatialAssociation (E : Type*)
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] :
    (E × PolarPoint) →L[ℝ] (E × ℝ) × ℝ :=
  ((ContinuousLinearMap.fst ℝ E PolarPoint).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint))).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)

theorem N01Properties.singleComponentFlowInverseCompose_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (u : CircleSpace S) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ) := by
  have heq : circleAffineInverse (fun _ => 0)
      (hN.singleComponentFlowCircle hS hT m x) m =
      Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f)
      (hN.singleComponentFlowCircle_affineLift hS hT m x hx hr)
  rw [circlePositiveInverseComposeLinear_decode _ _ _ _ _ _ _
    (hN.singleComponentFlowCircle_positive hS hT m x hx hr), heq]

include hχrange in
theorem N01Properties.singleComponentInterpolationInverseCompose_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Icc (C.left m) (C.right m)) (u : CircleSpace S) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.singleComponentInterpolationCircle hS hT χ m x) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (Function.invFun (returnInterpolation (χ m x.2)
          (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) θ) := by
  have heq : circleAffineInverse (fun _ => 0)
      (hN.singleComponentInterpolationCircle hS hT χ m x) m =
      Function.invFun (returnInterpolation (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f)
      (hN.singleComponentInterpolationCircle_lift hS hT χ m x hx)
  rw [circlePositiveInverseComposeLinear_decode _ _ _ _ _ _ _
    (hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m x hx hr), heq]

theorem N01Properties.singleComponentFlow_derivative_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
        (hN.singleComponentFlowCircle hS hT m x)) m θ =
      deriv (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ - 1 := by
  have heq : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentFlowCircle hS hT m x) m =
      fun t => C.minusFlow (liftSectorParameter S C x.1) m x.2 t - t := by
    rw [hN.singleComponentFlowCircle_decode hS hT m x hx hr]
    exact circleSingleComponentField_self m _
  have hf := hN.minusFlow_angular_contDiff hS hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x.1) m ⟨hr.1.le, hr.2.le⟩
  rw [circleDerivativeLinear_decode, heq]
  exact (((hf.differentiable (by simp) θ).hasDerivAt).sub (hasDerivAt_id θ)).deriv

def N01Properties.singleComponentPulledDisplacementCircle
    (m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ) : CircleSpace S :=
  circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0) (hN.singleComponentFlowCircle hS hT m (x.1.1, x.2))
    (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.singleComponentInterpolationCircle hS hT χ m (x.1.1, x.2))
      (hN.returnCorrectionDisplacementCircleLinear hS hT x.1.1 x.1.2))

include hχrange in
theorem N01Properties.singleComponentPulledDisplacementCircle_decode
    (m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ)
    (hx : x.1.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.singleComponentPulledDisplacementCircle hS hT χ m x) m θ =
      returnCorrectionDisplacementLinear S C (liftSectorParameter S C x.1.1) m
        (Function.invFun (returnInterpolation (χ m x.2)
          (returnCorrectionInitialMap S C (liftSectorParameter S C x.1.1) m))
            (Function.invFun (C.minusFlow (liftSectorParameter S C x.1.1) m x.2) θ)) x.1.2 := by
  unfold N01Properties.singleComponentPulledDisplacementCircle
  rw [hN.singleComponentFlowInverseCompose_decode hS hT m (x.1.1, x.2) hx hr,
    hN.singleComponentInterpolationInverseCompose_decode hS hT χ hχrange m
      (x.1.1, x.2) hx ⟨hr.1.le, hr.2.le⟩,
    hN.returnCorrectionDisplacementCircleLinear_decode hS hT x.1.1 hx]

def N01Properties.singleComponentInverseSlopeCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x)
    (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
      (hN.singleComponentFlowCircle hS hT m x))

theorem N01Properties.singleComponentInverseSlopeCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.singleComponentInverseSlopeCircle hS hT m x) m θ =
      deriv (C.minusFlow (liftSectorParameter S C x.1) m x.2)
        (Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ) - 1 := by
  unfold N01Properties.singleComponentInverseSlopeCircle
  rw [hN.singleComponentFlowInverseCompose_decode hS hT m x hx hr,
    hN.singleComponentFlow_derivative_decode hS hT m x hx hr]

def N01Properties.singleComponentVelocityCircle
    (m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ) : CircleSpace S :=
  circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m (deriv (χ m) x.2))
    (hN.singleComponentPulledDisplacementCircle hS hT χ m x +
      circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (hN.singleComponentInverseSlopeCircle hS hT m (x.1.1, x.2))
        (hN.singleComponentPulledDisplacementCircle hS hT χ m x))

include hχrange in
theorem N01Properties.singleComponentVelocityCircle_decode
    (m : ℕ) (x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ)
    (hx : x.1.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.singleComponentVelocityCircle hS hT χ m x) m θ =
      returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
        m (x.2, θ) x.1.2 := by
  unfold N01Properties.singleComponentVelocityCircle
  rw [circleProductBilinear_decode, circleSingletonLinear_decode, map_add]
  simp only [Pi.add_apply, circleSingletonField, if_pos rfl]
  rw [circleProductBilinear_decode,
    hN.singleComponentInverseSlopeCircle_decode hS hT m (x.1.1, x.2) hx hr,
    hN.singleComponentPulledDisplacementCircle_decode hS hT χ hχrange m x hx hr,
    returnCorrectionVelocityLinear_apply]
  ring

section JointTower

variable (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (m : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m)
  (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
    p.1 ∈ Ioo l h →
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a p *
          (originalCoefficients D S C (liftSectorParameter S C z)).c p)

def N01Properties.singleComponentVelocityCircleTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h)
      (hN.singleComponentVelocityCircle hS hT χ m) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hi : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hU := ((sectorNeighborhood_isOpen S base ε ε).prod
    (isOpen_univ : IsOpen (univ : Set (CircleSpace S)))).prod
      (isOpen_Ioo : IsOpen (Ioo l h))
  let L := correctionStateRadiusProjection S
  let P : (((StateDirections S × ℝ) × CircleSpace S) × ℝ) →L[ℝ]
      (StateDirections S × ℝ) × CircleSpace S :=
    ContinuousLinearMap.fst ℝ ((StateDirections S × ℝ) × CircleSpace S) ℝ
  let Q : (((StateDirections S × ℝ) × CircleSpace S) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ ((StateDirections S × ℝ) × CircleSpace S) ℝ
  have hL : MapsTo L ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h)
      (sectorNeighborhood S base ε ε ×ˢ Ioo l h) :=
    fun x hx => ⟨hx.1.1, hx.2⟩
  let Jflow := (hN.singleComponentFlowTower hS hT m l h hl hh hdisc).compLinear L hU hL
  let Jint := (hN.singleComponentInterpolationTower hS hT χ hχ m l h).compLinear L hU hL
  let Jdisp := (hN.smoothTameOn_returnCorrectionDisplacementCircleLinear hS hT).choose.compLinear
    P hU (fun x hx => hx.1)
  have hflowpos : MapsTo
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ =>
        hN.singleComponentFlowCircle hS hT m (L x))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h) (circlePositiveLiftDomain H) := by
    intro x hx
    exact hN.singleComponentFlowCircle_positive hS hT m (x.1.1, x.2) hx.1.1
      ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩
  have hintpos : MapsTo
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × ℝ =>
        hN.singleComponentInterpolationCircle hS hT χ m (L x))
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h) (circlePositiveLiftDomain H) := by
    intro x hx
    exact hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m
      (x.1.1, x.2) hx.1.1 ⟨(hl.trans hx.2.1).le, (hx.2.2.trans hh).le⟩
  let Jfirst := circleInverseComposeDirections hH hT hN.1.1 (by norm_num)
    hi (fun _ => 0) Jint Jdisp hintpos
  let Jpulled := circleInverseComposeDirections hH hT hN.1.1 (by norm_num)
    hi (fun _ => 0) Jflow Jfirst hflowpos
  let Jslope := circleInverseComposeDirections hH hT hN.1.1 (by norm_num)
    hi (fun _ => 0) Jflow (circleDerivativeDirections hH Jflow) hflowpos
  let Jprod := circleProductDirections hH hT hN.1.1 (by norm_num) hi Jslope Jpulled
  have hderχ : ContDiff ℝ ∞ (deriv (χ m)) := (contDiff_infty_iff_deriv.mp (hχ m)).2
  let Jcut := (smoothDirectionsOfContDiffOn isOpen_Ioo
    (hderχ.contDiffOn (s := Ioo l h))).compLinear Q hU (fun x hx => hx.2)
  exact circleProductDirections hH hT hN.1.1 (by norm_num) hi
    (circleSingletonDirections hH m Jcut) (smoothDirectionsAdd Jpulled Jprod)

def N01Properties.returnCorrectionVelocity_spatialJointTower :
    SmoothDirections (((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ Ioo l h) ×ˢ univ)
      (fun x : (((StateDirections S × ℝ) × CircleSpace S) × ℝ) × ℝ =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1.1)
          m (x.1.2, x.2) x.1.1.2) := by
  let J := hN.singleComponentVelocityCircleTower hS hT χ hχrange hχ m l h hl hh hdisc
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  apply (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m).congrOn
  intro x hx
  exact hN.singleComponentVelocityCircle_decode hS hT χ hχrange m x.1 hx.1.1.1
    ⟨hl.trans hx.1.2.1, hx.1.2.2.trans hh⟩ x.2

def N01Properties.returnCorrectionVelocity_parameterSpatialTower :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo l h ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
          m x.2 x.1.2) :=
  (hN.returnCorrectionVelocity_spatialJointTower hS hT χ hχrange hχ m l h hl hh hdisc).compLinear
    (parameterSpatialAssociation ((StateDirections S × ℝ) × CircleSpace S))
    (((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ).prod
      (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)

def N01Properties.singleComponentVelocityCircleAtResidualTower
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (fun x : (StateDirections S × ℝ) × ℝ =>
        hN.singleComponentVelocityCircle hS hT χ m
          ((x.1, R.residual (liftSectorParameter S C x.1)), x.2)) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo : IsOpen (Ioo l h))
  let F : ((StateDirections S × ℝ) × ℝ) →L[ℝ] StateDirections S × ℝ :=
    ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ℝ
  let G : ((StateDirections S × ℝ) × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ
  have hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) := by
    rcases hR with ⟨_, _, _, _, _, _, _, _, _, _, hr⟩
    exact hr
  let JR := hres.choose.compLinear F hU (fun x hx => hx.1)
  let J := smoothDirectionsProd
    (smoothDirectionsProd (smoothDirectionsLinearOn F hU) JR)
    (smoothDirectionsLinearOn G hU)
  exact J.compCircle hH
    (hN.singleComponentVelocityCircleTower hS hT χ hχrange hχ m l h hl hh hdisc)
    (fun x hx => ⟨⟨hx.1, mem_univ _⟩, hx.2⟩)

def N01Properties.returnCorrectionVelocity_actual_spatialJointTower
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε) :
    SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ Ioo l h) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
          m (x.1.2, x.2) (R.residual (liftSectorParameter S C x.1.1))) := by
  let J := hN.singleComponentVelocityCircleAtResidualTower hS hT χ hχrange hχ
    m l h hl hh hdisc hR
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  apply (circleDecodedJointDirections (hS.2.1 (3 / 4 : ℝ)) hH J m).congrOn
  intro x hx
  exact hN.singleComponentVelocityCircle_decode hS hT χ hχrange m
    ((x.1.1, R.residual (liftSectorParameter S C x.1.1)), x.1.2) hx.1.1
    ⟨hl.trans hx.1.2.1, hx.1.2.2.trans hh⟩ x.2

def N01Properties.returnCorrectionVelocity_actual_parameterSpatialTower
    {R : ReturnEquationData S} (hR : N02Properties D T S C R base ε) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1)
          m x.2 (R.residual (liftSectorParameter S C x.1))) :=
  (hN.returnCorrectionVelocity_actual_spatialJointTower hS hT χ hχrange hχ
    m l h hl hh hdisc hR).compLinear
    (parameterSpatialAssociation (StateDirections S × ℝ))
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)

end JointTower

end ContinuousFlexibility.Statements
