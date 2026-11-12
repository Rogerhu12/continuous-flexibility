import ContinuousFlexibility.Analysis.N01ReturnDisplacementSmoothTame
import ContinuousFlexibility.Analysis.N01InterpolationInverseCircle
import ContinuousFlexibility.Analysis.N01OpticalCutoffCircleMultiplier

/-!
# The actual cutoff velocity as a circle linear map

The independent displacement is pulled through the actual interpolation
inverse and the actual old-flow inverse. The old-flow angular derivative
is one plus a decoded circle field. Multiplying these two actual factors
and the derivative of the same cutoff gives exactly the original
independent-residual velocity, with a linear residual argument.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01ReturnVelocityCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

private theorem returnVelocity_decode_add_point
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (decode : V →ₗ[ℝ] (ℕ → ℝ → ℝ)) (u v : V) (m : ℕ) (θ : ℝ) :
    decode (u + v) m θ = decode u m θ + decode v m θ :=
  congrFun (congrFun (decode.map_add u v) m) θ

private theorem returnVelocity_reassemble
    {cut slope amplitude decodedSlope product displacement : ℝ}
    (hslope : decodedSlope = slope - 1)
    (hproduct : product = decodedSlope * amplitude)
    (hamplitude : amplitude = displacement) :
    cut * (amplitude + product) = slope * cut * displacement := by
  rw [hproduct, hslope, hamplitude]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowCircle_derivative_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
          (hN.endpointFlowCircle hS hT rsel hrsel z)) m θ =
      deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ - 1 := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz (le_refl ε)
  have hflow := hN.2.2.2.2.2.2.1 (liftSectorParameter S C z) hz' m θ
  have hpos : 0 < deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ :=
    ((hflow.2.2.2 (rsel m) (hrsel m))).1
  have hd : HasDerivAt
      ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z) m)
      (deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ - 1) θ := by
    apply ((differentiableAt_of_deriv_ne_zero hpos.ne').hasDerivAt.sub
      ((hasDerivAt_id θ).sub_const (opticalTravel D.w (C.left m) (rsel m)))).congr_of_eventuallyEq
    filter_upwards [] with t
    change (S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z) m t =
      C.minusFlow (liftSectorParameter S C z) m (rsel m) t -
        (t - opticalTravel D.w (C.left m) (rsel m))
    exact (hN.endpointFlowCircle_decode_apply hS hT rsel hrsel z hz m t).trans
      (congrArg (fun a : ℝ =>
        C.minusFlow (liftSectorParameter S C z) m (rsel m) t - a)
        (hN.minusFlow_reference_eq hS hT m (hrsel m) t))
  rw [circleDerivativeLinear_decode]
  exact hd.deriv

theorem N01Properties.selectorInverseComposeCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun i => -opticalTravel D.w (C.left i) (rsel i))
        (hN.endpointFlowCircle hS hT rsel hrsel z) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ) := by
  have hinv := congrFun (congrFun
    (hN.endpointFlowCircle_affineInverse hS hT rsel hrsel z hz) m) θ
  have hdecode := circlePositiveInverseComposeLinear_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun i => -opticalTravel D.w (C.left i) (rsel i))
    (hN.endpointFlowCircle hS hT rsel hrsel z) u
    (hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel z hz)
  exact (congrFun (congrFun hdecode m) θ).trans
    (congrArg ((S.circle (3 / 4 : ℝ)).decode u m) hinv)

theorem N01Properties.interpolationInverseComposeCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (Function.invFun (returnInterpolation (χ m (rsel m))
          (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) θ) := by
  have hinv : circleAffineInverse (fun _ => 0)
      (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) m θ =
      Function.invFun (returnInterpolation (χ m (rsel m))
        (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
      (hN.interpolationSelectorCircle_lift hS hT χ hχrange rsel hrsel z hz m)
  have hdecode := circlePositiveInverseComposeLinear_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
    (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) u
    (hN.interpolationSelectorCircle_positive hS hT χ hχrange rsel hrsel z hz)
  exact (congrFun (congrFun hdecode m) θ).trans
    (congrArg ((S.circle (3 / 4 : ℝ)).decode u m) hinv)

def N01Properties.selectorInverseSlopeCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun m => -opticalTravel D.w (C.left m) (rsel m))
    (hN.endpointFlowCircle hS hT rsel hrsel z)
    (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
      (hN.endpointFlowCircle hS hT rsel hrsel z))

theorem N01Properties.selectorInverseSlopeCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.selectorInverseSlopeCircle hS hT rsel hrsel z) m θ =
      deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m))
        (Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ) - 1 := by
  unfold N01Properties.selectorInverseSlopeCircle
  rw [hN.selectorInverseComposeCircle_decode hS hT rsel hrsel z hz,
    hN.endpointFlowCircle_derivative_decode hS hT rsel hrsel z hz]

def N01Properties.returnCorrectionPulledDisplacementCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S →ₗ[ℝ] CircleSpace S :=
  (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun m => -opticalTravel D.w (C.left m) (rsel m))
      (hN.endpointFlowCircle hS hT rsel hrsel z)).comp
    ((circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z)).comp
      (hN.returnCorrectionDisplacementCircleLinear hS hT z))

theorem N01Properties.returnCorrectionPulledDisplacementCircleLinear_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (ρ : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel z ρ) m θ =
      returnCorrectionDisplacementLinear S C (liftSectorParameter S C z) m
        (Function.invFun (returnInterpolation (χ m (rsel m))
          (returnCorrectionInitialMap S C (liftSectorParameter S C z) m))
          (Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ)) ρ := by
  let d : CircleSpace S := hN.returnCorrectionDisplacementCircleLinear hS hT z ρ
  let u : CircleSpace S :=
    circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) d
  let y : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ
  let x : ℝ := Function.invFun (returnInterpolation (χ m (rsel m))
    (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) y
  exact (hN.selectorInverseComposeCircle_decode hS hT rsel hrsel z hz u m θ).trans
    ((hN.interpolationInverseComposeCircle_decode hS hT χ hχrange rsel hrsel z hz d m y).trans
      (hN.returnCorrectionDisplacementCircleLinear_decode hS hT z hz ρ m x))

def N01Properties.returnCorrectionVelocityCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) : CircleSpace S →ₗ[ℝ] CircleSpace S :=
  (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff 1 rsel).comp
    ((LinearMap.id + circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (hN.selectorInverseSlopeCircle hS hT rsel hrsel z)).comp
      (hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel z))

theorem N01Properties.returnCorrectionVelocityCircleLinear_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ A * radialE (D.cellIndex (j m)) ^ P)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (ρ : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff rsel hrsel z ρ) m θ =
      returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C z) m (rsel m, θ) ρ := by
  let u : CircleSpace S :=
    hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel z ρ
  let a : CircleSpace S := hN.selectorInverseSlopeCircle hS hT rsel hrsel z
  let v : CircleSpace S :=
    circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) a u
  have hcut : (S.circle (3 / 4 : ℝ)).decode
      (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff 1 rsel (u + v)) m θ =
      deriv (χ m) (rsel m) * (S.circle (3 / 4 : ℝ)).decode (u + v) m θ :=
    (congrFun (congrFun
      (hN.opticalCutoffJetCircleLinear_decode hS hT j hcell χ hcutoff 1 rsel (u + v)) m) θ).trans
      (congrArg (fun c : ℝ => c * (S.circle (3 / 4 : ℝ)).decode (u + v) m θ)
        (congrFun (iteratedDeriv_one (f := χ m)) (rsel m)))
  have hadd := returnVelocity_decode_add_point (S.circle (3 / 4 : ℝ)).decode u v m θ
  have hprod : (S.circle (3 / 4 : ℝ)).decode v m θ =
      (S.circle (3 / 4 : ℝ)).decode a m θ * (S.circle (3 / 4 : ℝ)).decode u m θ :=
    congrFun (congrFun (circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ))
      hT hN.1.1 (by norm_num) a u) m) θ
  have hslope := hN.selectorInverseSlopeCircle_decode hS hT rsel hrsel z hz m θ
  have hamp := hN.returnCorrectionPulledDisplacementCircleLinear_decode
    hS hT χ hχrange rsel hrsel z hz ρ m θ
  exact hcut.trans
    ((congrArg (fun q : ℝ => deriv (χ m) (rsel m) * q) hadd).trans
      ((returnVelocity_reassemble (cut := deriv (χ m) (rsel m)) hslope hprod hamp).trans
        (returnCorrectionVelocityLinear_apply D S C χ (liftSectorParameter S C z)
          m (rsel m, θ) ρ).symm))

end ContinuousFlexibility.Statements
