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

private theorem velocitySpatial_pair_locallyConvex
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : WithSeminorms p) (hq : WithSeminorms q) :
    LocallyConvexSpace ℝ ((E × F) × ℝ) := by
  letI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  letI : LocallyConvexSpace ℝ F := hq.toLocallyConvexSpace
  infer_instance

private theorem returnVelocitySpatial_cutoff_product (c a u : ℝ) :
    c * (u + (a - 1) * u) = a * c * u := by
  ring

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
      (hN.singleComponentFlowCircle hS hT m x) m θ =
      Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
      (hN.singleComponentFlowCircle_affineLift hS hT m x hx hr)
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (circleAffineInverse (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x) m θ) :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circlePositiveInverseComposeLinear_decode
        (D := D) (T := T) (γ := (3 / 4 : ℝ)) (S := S.circle (3 / 4 : ℝ))
        (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
        (hN.singleComponentFlowCircle hS hT m x) u
        (hN.singleComponentFlowCircle_positive hS hT m x hx hr))
  exact hd.trans (congrArg (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode u m t) heq)

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
      (hN.singleComponentInterpolationCircle hS hT χ m x) m θ =
      Function.invFun (returnInterpolation (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
      (hN.singleComponentInterpolationCircle_lift hS hT χ m x hx)
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.singleComponentInterpolationCircle hS hT χ m x) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (circleAffineInverse (fun _ => 0)
          (hN.singleComponentInterpolationCircle hS hT χ m x) m θ) :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circlePositiveInverseComposeLinear_decode
        (D := D) (T := T) (γ := (3 / 4 : ℝ)) (S := S.circle (3 / 4 : ℝ))
        (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
        (hN.singleComponentInterpolationCircle hS hT χ m x) u
        (hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m x hx hr))
  exact hd.trans (congrArg (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode u m t) heq)

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
      fun t => C.minusFlow (liftSectorParameter S C x.1) m x.2 t - t :=
    (congrArg (fun f : ℕ → ℝ → ℝ => f m)
      (hN.singleComponentFlowCircle_decode hS hT m x hx hr)).trans
        (circleSingleComponentField_self m
          (fun t => C.minusFlow (liftSectorParameter S C x.1) m x.2 t - t))
  have hx' : liftSectorParameter S C x.1 ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood (C := C) hx (le_refl ε)
  have hf : ContDiff ℝ ∞ (C.minusFlow (liftSectorParameter S C x.1) m x.2) :=
    hN.minusFlow_angular_contDiff hS hT hx'
      (hN.2.2.1.liftSectorParameter_sector x.1) m ⟨hr.1.le, hr.2.le⟩
  have hder : deriv (fun t => C.minusFlow (liftSectorParameter S C x.1) m x.2 t - t) θ =
      deriv (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ - 1 :=
    (((hf.differentiable (by simp) θ).hasDerivAt).sub (hasDerivAt_id θ)).deriv
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
        (hN.singleComponentFlowCircle hS hT m x)) m θ =
      deriv ((S.circle (3 / 4 : ℝ)).decode (hN.singleComponentFlowCircle hS hT m x) m) θ :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circleDerivativeLinear_decode (hS.2.1 (3 / 4 : ℝ))
        (hN.singleComponentFlowCircle hS hT m x))
  exact hd.trans ((congrArg (fun f : ℝ → ℝ => deriv f θ) heq).trans hder)

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
  let v : CircleSpace S := hN.returnCorrectionDisplacementCircleLinear hS hT x.1.1 x.1.2
  let u : CircleSpace S :=
    circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.singleComponentInterpolationCircle hS hT χ m (x.1.1, x.2)) v
  let α : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C x.1.1) m x.2) θ
  let β : ℝ := Function.invFun (returnInterpolation (χ m x.2)
    (returnCorrectionInitialMap S C (liftSectorParameter S C x.1.1) m)) α
  have houter : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentPulledDisplacementCircle hS hT χ m x) m θ =
        (S.circle (3 / 4 : ℝ)).decode u m α :=
    hN.singleComponentFlowInverseCompose_decode hS hT m (x.1.1, x.2) hx hr u θ
  have hinner : (S.circle (3 / 4 : ℝ)).decode u m α =
      (S.circle (3 / 4 : ℝ)).decode v m β :=
    hN.singleComponentInterpolationInverseCompose_decode hS hT χ hχrange m
      (x.1.1, x.2) hx ⟨hr.1.le, hr.2.le⟩ v α
  have hv : (S.circle (3 / 4 : ℝ)).decode v m β =
      returnCorrectionDisplacementLinear S C (liftSectorParameter S C x.1.1) m β x.1.2 :=
    hN.returnCorrectionDisplacementCircleLinear_decode hS hT x.1.1 hx x.1.2 m β
  exact houter.trans (hinner.trans hv)

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
  let u : CircleSpace S := circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.singleComponentFlowCircle hS hT m x)
  let α : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ
  have houter : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentInverseSlopeCircle hS hT m x) m θ =
        (S.circle (3 / 4 : ℝ)).decode u m α :=
    hN.singleComponentFlowInverseCompose_decode hS hT m x hx hr u θ
  have hu : (S.circle (3 / 4 : ℝ)).decode u m α =
      deriv (C.minusFlow (liftSectorParameter S C x.1) m x.2) α - 1 :=
    hN.singleComponentFlow_derivative_decode hS hT m x hx hr α
  exact houter.trans hu

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
  let α : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C x.1.1) m x.2) θ
  let β : ℝ := Function.invFun (returnInterpolation (χ m x.2)
    (returnCorrectionInitialMap S C (liftSectorParameter S C x.1.1) m)) α
  let a : ℝ := deriv (C.minusFlow (liftSectorParameter S C x.1.1) m x.2) α
  let c : ℝ := deriv (χ m) x.2
  let d : ℝ := returnCorrectionDisplacementLinear S C (liftSectorParameter S C x.1.1)
    m β x.1.2
  let u : CircleSpace S := hN.singleComponentPulledDisplacementCircle hS hT χ m x
  let e : CircleSpace S := hN.singleComponentInverseSlopeCircle hS hT m (x.1.1, x.2)
  let b : CircleSpace S :=
    circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) e u
  let v : CircleSpace S := u + b
  let k : CircleSpace S := circleSingletonLinear (hS.2.1 (3 / 4 : ℝ)) m c
  have hk : (S.circle (3 / 4 : ℝ)).decode k m θ = c :=
    (congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circleSingletonLinear_decode (hS.2.1 (3 / 4 : ℝ)) m c)).trans (if_pos rfl)
  have hprod : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentVelocityCircle hS hT χ m x) m θ =
        (S.circle (3 / 4 : ℝ)).decode k m θ * (S.circle (3 / 4 : ℝ)).decode v m θ :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) k v)
  have hcut : (S.circle (3 / 4 : ℝ)).decode
      (hN.singleComponentVelocityCircle hS hT χ m x) m θ =
        c * (S.circle (3 / 4 : ℝ)).decode v m θ :=
    hprod.trans (congrArg (fun y : ℝ => y * (S.circle (3 / 4 : ℝ)).decode v m θ) hk)
  have hu : (S.circle (3 / 4 : ℝ)).decode u m θ = d :=
    hN.singleComponentPulledDisplacementCircle_decode hS hT χ hχrange m x hx hr θ
  have he : (S.circle (3 / 4 : ℝ)).decode e m θ = a - 1 :=
    hN.singleComponentInverseSlopeCircle_decode hS hT m (x.1.1, x.2) hx hr θ
  have hb : (S.circle (3 / 4 : ℝ)).decode b m θ = (a - 1) * d :=
    (congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) e u)).trans
        (congrArg₂ (fun y z : ℝ => y * z) he hu)
  have hsum : (S.circle (3 / 4 : ℝ)).decode v m θ =
      (S.circle (3 / 4 : ℝ)).decode u m θ + (S.circle (3 / 4 : ℝ)).decode b m θ :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ) ((S.circle (3 / 4 : ℝ)).decode.map_add u b)
  have hv : (S.circle (3 / 4 : ℝ)).decode v m θ = d + (a - 1) * d :=
    hsum.trans (congrArg₂ (fun y z : ℝ => y + z) hu hb)
  have htarget : returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1)
      m (x.2, θ) x.1.2 = a * c * d :=
    returnCorrectionVelocityLinear_apply D S C χ (liftSectorParameter S C x.1.1)
      m (x.2, θ) x.1.2
  exact hcut.trans (((congrArg (fun y : ℝ => c * y) hv).trans
    (returnVelocitySpatial_cutoff_product c a d)).trans htarget.symm)

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
  letI : LocallyConvexSpace ℝ (((StateDirections S × ℝ) × H.Space) × ℝ) :=
    velocitySpatial_pair_locallyConvex (E := StateDirections S × ℝ) (F := H.Space)
      (sectorPairGrading_withSeminorms S)
      (withSeminorms_graded (fun n => H.level n) H.bond)
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
