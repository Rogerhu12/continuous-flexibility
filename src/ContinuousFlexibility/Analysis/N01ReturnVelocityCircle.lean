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
  have hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood (C := C) hz (le_refl ε)
  have hflow := hN.2.2.2.2.2.2.1 (liftSectorParameter S C z) hz' m θ
  have hpos : 0 < deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ :=
    ((hflow.2.2.2 (rsel m) (hrsel m))).1
  have hd : HasDerivAt
      ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel z) m)
      (deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ - 1) θ := by
    apply ((differentiableAt_of_deriv_ne_zero hpos.ne').hasDerivAt.sub
      ((hasDerivAt_id θ).sub_const (opticalTravel D.w (C.left m) (rsel m)))).congr_of_eventuallyEq
    filter_upwards [] with t
    simp only [Pi.sub_apply, id_eq]
    exact (hN.endpointFlowCircle_decode_apply hS hT rsel hrsel z hz m t).trans
      (congrArg (fun a : ℝ => C.minusFlow (liftSectorParameter S C z) m (rsel m) t - a)
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
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun i => -opticalTravel D.w (C.left i) (rsel i))
        (hN.endpointFlowCircle hS hT rsel hrsel z) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (circleAffineInverse (fun i => -opticalTravel D.w (C.left i) (rsel i))
          (hN.endpointFlowCircle hS hT rsel hrsel z) m θ) :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circlePositiveInverseComposeLinear_decode
        (D := D) (T := T) (γ := (3 / 4 : ℝ)) (S := S.circle (3 / 4 : ℝ))
        (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun i => -opticalTravel D.w (C.left i) (rsel i))
        (hN.endpointFlowCircle hS hT rsel hrsel z) u
        (hN.endpointFlowCircle_mem_positiveLiftDomain hS hT rsel hrsel z hz))
  have hinv : circleAffineInverse (fun i => -opticalTravel D.w (C.left i) (rsel i))
      (hN.endpointFlowCircle hS hT rsel hrsel z) m θ =
        Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (hN.endpointFlowCircle_affineInverse hS hT rsel hrsel z hz)
  exact hd.trans (congrArg (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode u m t) hinv)

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
  have hd : (S.circle (3 / 4 : ℝ)).decode
      (circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) u) m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (circleAffineInverse (fun _ => 0)
          (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) m θ) :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circlePositiveInverseComposeLinear_decode
        (D := D) (T := T) (γ := (3 / 4 : ℝ)) (S := S.circle (3 / 4 : ℝ))
        (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0)
        (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) u
        (hN.interpolationSelectorCircle_positive hS hT χ hχrange rsel hrsel z hz))
  exact hd.trans (congrArg (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode u m t) hinv)

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

private theorem returnVelocityCircle_cutoff_product (c a u : ℝ) :
    c * (u + (a - 1) * u) = a * c * u := by
  ring

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
  let v : CircleSpace S := hN.returnCorrectionDisplacementCircleLinear hS hT z ρ
  let u : CircleSpace S :=
    circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.interpolationSelectorCircle hS hT χ hχrange rsel hrsel z) v
  let α : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ
  let β : ℝ := Function.invFun (returnInterpolation (χ m (rsel m))
    (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) α
  have houter : (S.circle (3 / 4 : ℝ)).decode
      (hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel z ρ) m θ =
        (S.circle (3 / 4 : ℝ)).decode u m α := by
    simp only [N01Properties.returnCorrectionPulledDisplacementCircleLinear,
      LinearMap.comp_apply]
    exact hN.selectorInverseComposeCircle_decode hS hT rsel hrsel z hz u m θ
  have hinner : (S.circle (3 / 4 : ℝ)).decode u m α =
      (S.circle (3 / 4 : ℝ)).decode v m β :=
    hN.interpolationInverseComposeCircle_decode hS hT χ hχrange rsel hrsel z hz v m α
  have hv : (S.circle (3 / 4 : ℝ)).decode v m β =
      returnCorrectionDisplacementLinear S C (liftSectorParameter S C z) m β ρ :=
    hN.returnCorrectionDisplacementCircleLinear_decode hS hT z hz ρ m β
  exact houter.trans (hinner.trans hv)

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
  let α : ℝ := Function.invFun (C.minusFlow (liftSectorParameter S C z) m (rsel m)) θ
  let β : ℝ := Function.invFun (returnInterpolation (χ m (rsel m))
    (returnCorrectionInitialMap S C (liftSectorParameter S C z) m)) α
  let a : ℝ := deriv (C.minusFlow (liftSectorParameter S C z) m (rsel m)) α
  let c : ℝ := deriv (χ m) (rsel m)
  let d : ℝ := returnCorrectionDisplacementLinear S C (liftSectorParameter S C z) m β ρ
  let u : CircleSpace S :=
    hN.returnCorrectionPulledDisplacementCircleLinear hS hT χ hχrange rsel hrsel z ρ
  let e : CircleSpace S := hN.selectorInverseSlopeCircle hS hT rsel hrsel z
  let b : CircleSpace S :=
    circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) e u
  let v : CircleSpace S := u + b
  have hcutPoint : (S.circle (3 / 4 : ℝ)).decode
      (hN.opticalCutoffJetCircleLinear hS hT j hcell χ hcutoff 1 rsel v) m θ =
        c * (S.circle (3 / 4 : ℝ)).decode v m θ := by
    simpa only [iteratedDeriv_one] using
      (congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
        (hN.opticalCutoffJetCircleLinear_decode hS hT j hcell χ hcutoff 1 rsel v))
  have hcut : (S.circle (3 / 4 : ℝ)).decode
      (hN.returnCorrectionVelocityCircleLinear hS hT j hcell χ hχrange hcutoff rsel hrsel z ρ)
        m θ = c * (S.circle (3 / 4 : ℝ)).decode v m θ := by
    simp only [N01Properties.returnCorrectionVelocityCircleLinear, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.id_apply]
    exact hcutPoint
  have hu : (S.circle (3 / 4 : ℝ)).decode u m θ = d :=
    hN.returnCorrectionPulledDisplacementCircleLinear_decode hS hT χ hχrange rsel hrsel z hz ρ m θ
  have he : (S.circle (3 / 4 : ℝ)).decode e m θ = a - 1 :=
    hN.selectorInverseSlopeCircle_decode hS hT rsel hrsel z hz m θ
  have hb : (S.circle (3 / 4 : ℝ)).decode b m θ = (a - 1) * d :=
    (congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) e u)).trans
        (congrArg₂ (fun x y : ℝ => x * y) he hu)
  have hsum : (S.circle (3 / 4 : ℝ)).decode v m θ =
      (S.circle (3 / 4 : ℝ)).decode u m θ + (S.circle (3 / 4 : ℝ)).decode b m θ :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ) ((S.circle (3 / 4 : ℝ)).decode.map_add u b)
  have hv : (S.circle (3 / 4 : ℝ)).decode v m θ = d + (a - 1) * d :=
    hsum.trans (congrArg₂ (fun x y : ℝ => x + y) hu hb)
  have htarget : returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C z)
      m (rsel m, θ) ρ = a * c * d :=
    returnCorrectionVelocityLinear_apply D S C χ (liftSectorParameter S C z) m (rsel m, θ) ρ
  exact hcut.trans (((congrArg (fun x : ℝ => c * x) hv).trans
    (returnVelocityCircle_cutoff_product c a d)).trans htarget.symm)

end ContinuousFlexibility.Statements
