import ContinuousFlexibility.Analysis.N01ReturnVelocitySpatialTower
import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegrals

/-!
# The same first integral with a variable physical radius

The existing single-component circle towers carry the actual ordinary
flow and the actual cutoff interpolation. Their genuine inverse operators
are composed with the given left chart. Decoding yields the literal
inverse of the same corrected flow, jointly in state, radius and angle.
Only the real original-coefficient discriminant on the chosen strip is
an input; no parameter tower or inverse regularity is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local instance n04MinusFirstIntegralStripStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem invFun_comp_of_bijective {f g : ℝ → ℝ}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.invFun (fun t => f (g t)) =
      fun t => Function.invFun g (Function.invFun f t) := by
  apply Function.invFun_eq_of_injective_of_rightInverse (hf.1.comp hg.1)
  intro t
  change f (g (Function.invFun g (Function.invFun f t))) = t
  rw [Function.rightInverse_invFun hg.2, Function.rightInverse_invFun hf.2]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (χ : ℕ → ℝ → ℝ)
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)

include hN hS hT hχrange in
private theorem correctedFlow_inverse_comp
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) :
    Function.invFun (returnCorrectedMinusFlow S C χ (liftSectorParameter S C x.1) m x.2) =
      fun θ => Function.invFun (returnInterpolation (χ m x.2)
        (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m))
          (Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hbij (u : H.Space) (hu : u ∈ circlePositiveLiftDomain H)
      (f : ℝ → ℝ) (hf : circleAffineLift (fun _ => 0) (H.decode u) 1 m = f) :
      Function.Bijective f := by
    rw [← hf]
    exact ⟨(strictMono_of_deriv_pos
      ((circlePositiveLiftDomain_iff hH (fun _ => 0) u).mp hu m)).injective,
      circleAffineLift_surjective hH hT hN.1.1 (by norm_num) (fun _ => 0) u m⟩
  have hf := hbij (hN.singleComponentFlowCircle hS hT m x)
    (hN.singleComponentFlowCircle_positive hS hT m x hx hr) _
    (hN.singleComponentFlowCircle_affineLift hS hT m x hx hr)
  have hg := hbij (hN.singleComponentInterpolationCircle hS hT χ m x)
    (hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m x hx
      ⟨hr.1.le, hr.2.le⟩) _
    (hN.singleComponentInterpolationCircle_lift hS hT χ m x hx)
  exact invFun_comp_of_bijective hf hg

/-- The initial-chart displacement transported through the actual
cutoff interpolation. -/
def N01Properties.n04NegativeGeometryInitialFirstIntegralCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  hN.singleComponentInterpolationInverseCircle hS hT χ m x +
    circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.singleComponentInterpolationCircle hS hT χ m x)
      x.1.1.val.2.2.2

/-- The circle displacement of the actual first integral, before taking
its state-and-angle tower. -/
def N01Properties.n04NegativeGeometryMinusFirstIntegralCircle
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ) : CircleSpace S :=
  hN.singleComponentFlowInverseCircle hS hT m x +
    circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x)
      (hN.n04NegativeGeometryInitialFirstIntegralCircle hS hT χ m x)

private theorem circle_decode_add_eval (H : CircleModelData)
    (e c : H.Space) (m : ℕ) (θ : ℝ) :
    H.decode (e + c) m θ = H.decode e m θ + H.decode c m θ :=
  congrArg (fun f : ℕ → ℝ → ℝ => f m θ) (H.decode.map_add e c)

include hχrange in
private theorem initialFirstIntegralCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    let v := Function.invFun (returnInterpolation (χ m x.2)
      (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) θ
    (S.circle (3 / 4 : ℝ)).decode
        (hN.n04NegativeGeometryInitialFirstIntegralCircle hS hT χ m x) m θ =
      (v - θ) + (S.circle (3 / 4 : ℝ)).decode x.1.1.val.2.2.2 m v := by
  let H := S.circle (3 / 4 : ℝ)
  let v := Function.invFun (returnInterpolation (χ m x.2)
    (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) θ
  let e : CircleSpace S := hN.singleComponentInterpolationInverseCircle hS hT χ m x
  let c : CircleSpace S := circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ))
    hT hN.1.1 (by norm_num) (fun _ => 0)
      (hN.singleComponentInterpolationCircle hS hT χ m x) x.1.1.val.2.2.2
  have he : H.decode e m θ = v - θ :=
    hN.singleComponentInterpolationInverseCircle_decode
      hS hT χ hχrange m x hx ⟨hr.1.le, hr.2.le⟩ θ
  have hc : H.decode c m θ = H.decode x.1.1.val.2.2.2 m v :=
    hN.singleComponentInterpolationInverseCompose_decode
      hS hT χ hχrange m x hx ⟨hr.1.le, hr.2.le⟩ x.1.1.val.2.2.2 θ
  exact (circle_decode_add_eval H e c m θ).trans
    (congrArg₂ (fun a b : ℝ => a + b) he hc)

include hχrange in
private theorem correctedFirstIntegralCircle_displacement
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    let u := Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ
    let v := Function.invFun (returnInterpolation (χ m x.2)
      (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) u
    (S.circle (3 / 4 : ℝ)).decode
        (hN.n04NegativeGeometryMinusFirstIntegralCircle hS hT χ m x) m θ =
      (u - θ) + ((v - u) + (S.circle (3 / 4 : ℝ)).decode x.1.1.val.2.2.2 m v) := by
  let H := S.circle (3 / 4 : ℝ)
  let u := Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ
  let c : CircleSpace S := hN.n04NegativeGeometryInitialFirstIntegralCircle hS hT χ m x
  let d : CircleSpace S := circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ))
    hT hN.1.1 (by norm_num) (fun _ => 0) (hN.singleComponentFlowCircle hS hT m x) c
  have he : H.decode (hN.singleComponentFlowInverseCircle hS hT m x) m θ = u - θ :=
    hN.singleComponentFlowInverseCircle_decode hS hT m x hx hr θ
  have hd : H.decode d m θ = H.decode c m u :=
    hN.singleComponentFlowInverseCompose_decode hS hT m x hx hr c θ
  have hc := initialFirstIntegralCircle_decode hN hS hT χ hχrange m x hx hr u
  exact (circle_decode_add_eval H (hN.singleComponentFlowInverseCircle hS hT m x)
    d m θ).trans (congrArg₂ (fun a b : ℝ => a + b) he (hd.trans hc))

private theorem firstIntegral_displacement_cancel (θ u v d : ℝ) :
    θ + 0 + ((u - θ) + ((v - u) + d)) = v + d := by ring

include hχrange in
private theorem correctedFirstIntegralCircle_decode
    (m : ℕ) (x : (StateDirections S × ℝ) × ℝ)
    (hx : x.1 ∈ sectorNeighborhood S base ε ε)
    (hr : x.2 ∈ Ioo (C.left m) (C.right m)) (θ : ℝ) :
    θ + 0 + (S.circle (3 / 4 : ℝ)).decode
      (hN.n04NegativeGeometryMinusFirstIntegralCircle hS hT χ m x) m θ =
      n04bMinusFirstIntegral
        (fun q => returnCorrectedMinusFlow S C χ (liftSectorParameter S C x.1) m q.1 q.2)
        (stateLeftChart S (liftSectorParameter S C x.1).1 m) (x.2, θ) := by
  let H := S.circle (3 / 4 : ℝ)
  let u : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C x.1) m x.2) θ
  let v : ℝ := Function.invFun (returnInterpolation (χ m x.2)
    (returnCorrectionInitialMap S C (liftSectorParameter S C x.1) m)) u
  have hdecode : H.decode
      (hN.n04NegativeGeometryMinusFirstIntegralCircle hS hT χ m x) m θ =
      (u - θ) + ((v - u) + H.decode x.1.1.val.2.2.2 m v) :=
    correctedFirstIntegralCircle_displacement hN hS hT χ hχrange m x hx hr θ
  have hleft : stateLeftChart S (liftSectorParameter S C x.1).1 m v =
      v + H.decode x.1.1.val.2.2.2 m v :=
    hN.2.2.1.sector_leftChart x.1 m v
  have hinverse : Function.invFun (returnCorrectedMinusFlow S C χ
      (liftSectorParameter S C x.1) m x.2) θ = v :=
    congrFun (correctedFlow_inverse_comp hN hS hT χ hχrange m x hx hr) θ
  have hrecover : stateLeftChart S (liftSectorParameter S C x.1).1 m
      (Function.invFun (returnCorrectedMinusFlow S C χ
        (liftSectorParameter S C x.1) m x.2) θ) =
      v + H.decode x.1.1.val.2.2.2 m v :=
    (congrArg (stateLeftChart S (liftSectorParameter S C x.1).1 m) hinverse).trans hleft
  exact (congrArg (fun d : ℝ => θ + 0 + d) hdecode).trans
    ((firstIntegral_displacement_cancel θ u v (H.decode x.1.1.val.2.2.2 m v)).trans
      hrecover.symm)

/-- One genuine joint tower for the actual first integral on an interior
physical strip. The cutoff, old flow and inverse are all retained. -/
def N01Properties.n04NegativeGeometryMinusFirstIntegral_stripJointTower
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m)) (m : ℕ) (l h : ℝ)
    (hl : C.left m < l) (hh : h < C.right m)
    (hdisc : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ p : PolarPoint,
      p.1 ∈ Ioo l h →
        0 < (originalCoefficients D S C (liftSectorParameter S C z)).b p ^ 2 -
          (originalCoefficients D S C (liftSectorParameter S C z)).a p *
            (originalCoefficients D S C (liftSectorParameter S C z)).c p) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (Ioo l h ×ˢ univ))
      (fun x : (StateDirections S × ℝ) × PolarPoint => n04bMinusFirstIntegral
        (fun q => returnCorrectedMinusFlow S C χ (liftSectorParameter S C x.1) m q.1 q.2)
        (stateLeftChart S (liftSectorParameter S C x.1).1 m) x.2) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hi := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hU := (sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo : IsOpen (Ioo l h))
  let F : ((StateDirections S × ℝ) × ℝ) →L[ℝ] StateDirections S × ℝ :=
    ContinuousLinearMap.fst ℝ (StateDirections S × ℝ) ℝ
  let Jleft := (smoothTameOn_sectorChart S).choose.compLinear F hU
    (fun _ _ => mem_univ _)
  let Jflow := hN.singleComponentFlowTower hS hT m l h hl hh hdisc
  let Kflow := hN.singleComponentFlowInverseTower hS hT m l h hl hh hdisc
  let Jinitial := hN.singleComponentInterpolationTower hS hT χ hχ m l h
  let Kinitial := hN.singleComponentInterpolationInverseTower
    hS hT χ hχ hχrange m l h hl hh
  have hflowpos : MapsTo (hN.singleComponentFlowCircle hS hT m)
      (sectorNeighborhood S base ε ε ×ˢ Ioo l h) (circlePositiveLiftDomain H) :=
    fun x hx => hN.singleComponentFlowCircle_positive hS hT m x hx.1
      ⟨hl.trans hx.2.1, hx.2.2.trans hh⟩
  have hinitialpos : MapsTo (hN.singleComponentInterpolationCircle hS hT χ m)
      (sectorNeighborhood S base ε ε ×ˢ Ioo l h) (circlePositiveLiftDomain H) :=
    fun x hx => hN.singleComponentInterpolationCircle_positive hS hT χ hχrange m x hx.1
      ⟨(hl.trans hx.2.1).le, (hx.2.2.trans hh).le⟩
  let A := smoothDirectionsAdd Kinitial
    (circleInverseComposeDirections hH hT hN.1.1 (by norm_num) hi (fun _ => 0)
      Jinitial Jleft hinitialpos)
  let B : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ Ioo l h)
      (hN.n04NegativeGeometryMinusFirstIntegralCircle hS hT χ m) := by
    unfold n04NegativeGeometryMinusFirstIntegralCircle n04NegativeGeometryInitialFirstIntegralCircle
    exact smoothDirectionsAdd Kflow
      (circleInverseComposeDirections hH hT hN.1.1 (by norm_num) hi (fun _ => 0)
        Jflow A hflowpos)
  have hsample (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 i
  let K := circleAffineLiftJointDirections hH hsample B (fun _ => 0) m
  have hdecode : SmoothDirections ((sectorNeighborhood S base ε ε ×ˢ Ioo l h) ×ˢ univ)
      (fun x : ((StateDirections S × ℝ) × ℝ) × ℝ => n04bMinusFirstIntegral
        (fun q => returnCorrectedMinusFlow S C χ (liftSectorParameter S C x.1.1) m q.1 q.2)
        (stateLeftChart S (liftSectorParameter S C x.1.1).1 m) (x.1.2, x.2)) := by
    apply K.congrOn
    intro x hx
    have hr : x.1.2 ∈ Ioo (C.left m) (C.right m) :=
      ⟨hl.trans hx.1.2.1, hx.1.2.2.trans hh⟩
    exact correctedFirstIntegralCircle_decode hN hS hT χ hχrange
      m x.1 hx.1.1 hr x.2
  exact hdecode.compLinear (parameterSpatialAssociation (StateDirections S × ℝ))
    ((sectorNeighborhood_isOpen S base ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)

end ContinuousFlexibility.Statements
