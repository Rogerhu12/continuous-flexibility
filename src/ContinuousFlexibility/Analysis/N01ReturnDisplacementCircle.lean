import ContinuousFlexibility.Analysis.N01ReturnInverseCircle
import ContinuousFlexibility.Analysis.CircleAveragedComposition
import ContinuousFlexibility.Analysis.CircleWeightedProduct
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualLinear

/-!
# The actual independent-residual displacement as a circle linear map

The removable divided difference is evaluated by its true derivative
integral. The affine part of the inverse contributes one, and the
remaining integral is the existing averaged composition of a decoded
circle derivative. Multiplication and the actual forward return chart
then realize exactly the original displacement linear map, including
at zeros of the residual.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01ReturnDisplacementCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff

private theorem returnCircle_affine_reassemble {value angle travel displacement : ℝ}
    (h : displacement = value - (angle - travel)) :
    angle + -travel + displacement = value := by
  linarith only [h]

private theorem returnCircle_sum_reassemble {a b forward value angle travel : ℝ}
    (ha : a = forward - (angle - travel)) (hb : forward + b = value) :
    a + b = value - (angle - travel) := by
  linarith only [ha, hb]

private theorem returnCircle_decode_add_point
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (decode : V →ₗ[ℝ] (ℕ → ℝ → ℝ)) (u v : V) (m : ℕ) (θ : ℝ) :
    decode (u + v) m θ = decode u m θ + decode v m θ :=
  congrFun (congrFun (decode.map_add u v) m) θ

private theorem returnCircle_integral_dslope
    (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (θ d : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hderiv : ∀ t, f t = deriv G (θ + t * d) - 1) :
    (∫ t in (0 : ℝ)..1, f t) = dslope G θ (θ + d) - 1 := by
  have hi : (∫ t in (0 : ℝ)..1, deriv G (θ + t * d)) =
      1 + ∫ t in (0 : ℝ)..1, f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (1 + f t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hd := hderiv t
        linarith only [hd]
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable 0 1)
          (hf.intervalIntegrable 0 1), intervalIntegral.integral_const]
        simp only [sub_zero, one_smul]
  rw [returnCorrection_dslope_integral hG θ d, hi]
  ring

private theorem returnCircle_average_substitute
    (g : ℝ → ℝ) (θ r d : ℝ) (hr : r = d) :
    (∫ t in (0 : ℝ)..1, g (θ + 0 + t * r)) =
      ∫ t in (0 : ℝ)..1, g (θ + t * d) := by
  rw [hr]
  simp only [add_zero]

private theorem returnCircle_product_reassemble {a slope q : ℝ}
    (ha : a = slope - 1) :
    q + a * q = slope * q := by
  rw [ha]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The actual map `rightChartCandidate ∘ minusReturn`, minus its fixed
negative optical translation and the identity. -/
def N01Properties.rightReturnChartCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  hN.returnFlowCircle hS hT z +
    circleShiftedChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun m => -C.travel m) (hN.returnFlowCircle hS hT z)
      (circleOddLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z))

theorem N01Properties.rightReturnChartCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.rightReturnChartCircle hS hT z) m θ =
      rightChartCandidate S C (liftSectorParameter S C z) m
        (C.minusFlow (liftSectorParameter S C z) m (C.right m) θ) - (θ - C.travel m) := by
  let e : CircleSpace S := hN.returnFlowCircle hS hT z
  let u : CircleSpace S :=
    circleOddLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z)
  let v : CircleSpace S := circleShiftedChartComposeLinear
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun m => -C.travel m) e u
  have ha := hN.returnFlowCircle_decode hS hT z hz m θ
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode e m θ =
      C.minusFlow (liftSectorParameter S C z) m (C.right m) θ :=
    returnCircle_affine_reassemble ha
  have hk := congrFun (hN.sectorReturnTransportCircle_odd_lift hS hT z hz m)
    (C.minusFlow (liftSectorParameter S C z) m (C.right m) θ)
  simp only [circleAffineLift, add_zero, one_mul] at hk
  have hcomp : (S.circle (3 / 4 : ℝ)).decode v m θ =
      (S.circle (3 / 4 : ℝ)).decode u m
        (C.minusFlow (liftSectorParameter S C z) m (C.right m) θ) :=
    (circleShiftedChartComposeLinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
      (by norm_num) (fun m => -C.travel m) e u m θ).trans
        (congrArg ((S.circle (3 / 4 : ℝ)).decode u m) heval)
  exact (returnCircle_decode_add_point (S.circle (3 / 4 : ℝ)).decode e v m θ).trans
    ((congrArg (fun a : ℝ => (S.circle (3 / 4 : ℝ)).decode e m θ + a) hcomp).trans
      (returnCircle_sum_reassemble ha hk))

theorem N01Properties.smoothTameOn_rightReturnChartCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.rightReturnChartCircle hS hT) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp := sectorPairGrading_monotone S
  have ht := sectorPairGrading_withSeminorms S
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  have hU := sectorNeighborhood_isOpen S base ε ε
  have hodd : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => circleOddLinear hH (hN.sectorReturnTransportCircle hS hT z)) :=
    smoothTameOn_comp_topological hp ht htop hU isOpen_univ (fun _ _ => mem_univ _)
      (hN.smoothTameOn_sectorReturnTransportCircle hS hT)
      (smoothTameOn_circleOddLinear hH)
  have hflow := hN.smoothTameOn_returnFlowCircle hS hT
  have hcomp := smoothTameOn_circleShiftedChartCompose_maps hH hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun m => -C.travel m) hp ht hU hflow hodd
  exact smoothTameOn_add hp hflow hcomp

theorem N01Properties.returnTransportInverseCircle_derivative_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
          (hN.returnTransportInverseCircle hS hT z)) m θ =
      deriv (fun t => C.minusReturnInverse (liftSectorParameter S C z) m
        (C.rightChartInverse (liftSectorParameter S C z) m t)) θ - 1 := by
  let G : ℝ → ℝ := fun t => C.minusReturnInverse (liftSectorParameter S C z) m
    (C.rightChartInverse (liftSectorParameter S C z) m t)
  have hG : ContDiff ℝ ∞ G := hN.returnTransportInverse_contDiff hS hT
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z) m
  have hd : HasDerivAt
      ((S.circle (3 / 4 : ℝ)).decode (hN.returnTransportInverseCircle hS hT z) m)
      (deriv G θ - 1) θ := by
    apply (((hG.differentiable (by simp)) θ).hasDerivAt.sub
      ((hasDerivAt_id θ).add_const (C.travel m))).congr_of_eventuallyEq
    exact Eventually.of_forall (fun t => hN.returnTransportInverseCircle_decode hS hT z hz m t)
  rw [circleDerivativeLinear_decode]
  exact hd.deriv

/-- The actual divided difference of the inverse coordinate, minus its
constant affine part, in the original circle model. -/
def N01Properties.returnCorrectionDslopeCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circleAverageComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0) (hN.sectorReturnResidualCircle hS hT z)
    (circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
      (hN.returnTransportInverseCircle hS hT z))

theorem N01Properties.returnCorrectionDslopeCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    let G : ℝ → ℝ := fun t => C.minusReturnInverse (liftSectorParameter S C z) m
      (C.rightChartInverse (liftSectorParameter S C z) m t)
    (S.circle (3 / 4 : ℝ)).decode (hN.returnCorrectionDslopeCircle hS hT z) m θ =
      dslope G θ (θ + returnResidualField S C (liftSectorParameter S C z) m θ) - 1 := by
  let G : ℝ → ℝ := fun t => C.minusReturnInverse (liftSectorParameter S C z) m
    (C.rightChartInverse (liftSectorParameter S C z) m t)
  let d : ℝ := returnResidualField S C (liftSectorParameter S C z) m θ
  let u : CircleSpace S := circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.returnTransportInverseCircle hS hT z)
  let f : ℝ → ℝ := fun t => (S.circle (3 / 4 : ℝ)).decode u m (θ + t * d)
  have hG : ContDiff ℝ ∞ G := hN.returnTransportInverse_contDiff hS hT
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z) m
  have hf : Continuous f := (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 u).1 m).1.continuous.comp
    (continuous_const.add (continuous_id.mul continuous_const))
  have hderiv (t : ℝ) : f t = deriv G (θ + t * d) - 1 :=
    hN.returnTransportInverseCircle_derivative_decode hS hT z hz m (θ + t * d)
  have havg : (S.circle (3 / 4 : ℝ)).decode
      (hN.returnCorrectionDslopeCircle hS hT z) m θ = ∫ t in (0 : ℝ)..1, f t :=
    (circleAverageComposeLinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
      (by norm_num) (fun _ => 0) (hN.sectorReturnResidualCircle hS hT z) u m θ).trans
        (returnCircle_average_substitute ((S.circle (3 / 4 : ℝ)).decode u m) θ
          ((S.circle (3 / 4 : ℝ)).decode (hN.sectorReturnResidualCircle hS hT z) m θ) d
          (hN.sectorReturnResidualCircle_decode hS hT z hz m θ))
  exact havg.trans (returnCircle_integral_dslope G (hG.of_le (by simp)) θ d f hf hderiv)

def N01Properties.returnCorrectionDisplacementCircleLinear
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S →ₗ[ℝ] CircleSpace S :=
  (circleShiftedChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun m => -C.travel m) (hN.rightReturnChartCircle hS hT z)).comp
    (LinearMap.id + circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (hN.returnCorrectionDslopeCircle hS hT z))

theorem N01Properties.returnCorrectionDisplacementCircleLinear_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (ρ : CircleSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.returnCorrectionDisplacementCircleLinear hS hT z ρ) m θ =
      returnCorrectionDisplacementLinear S C (liftSectorParameter S C z) m θ ρ := by
  let y : ℝ := rightChartCandidate S C (liftSectorParameter S C z) m
    (C.minusFlow (liftSectorParameter S C z) m (C.right m) θ)
  let e : CircleSpace S := hN.rightReturnChartCircle hS hT z
  let a : CircleSpace S := hN.returnCorrectionDslopeCircle hS hT z
  let v : CircleSpace S :=
    circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) a ρ
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode e m θ = y :=
    returnCircle_affine_reassemble (hN.rightReturnChartCircle_decode hS hT z hz m θ)
  have hshift := (circleShiftedChartComposeLinear_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun m => -C.travel m) e (ρ + v) m θ).trans
      (congrArg ((S.circle (3 / 4 : ℝ)).decode (ρ + v) m) heval)
  have hprod : (S.circle (3 / 4 : ℝ)).decode v m y =
      (S.circle (3 / 4 : ℝ)).decode a m y * (S.circle (3 / 4 : ℝ)).decode ρ m y :=
    congrFun (congrFun (circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ))
      hT hN.1.1 (by norm_num) a ρ) m) y
  have hadd := returnCircle_decode_add_point (S.circle (3 / 4 : ℝ)).decode ρ v m y
  have hds := hN.returnCorrectionDslopeCircle_decode hS hT z hz m y
  exact hshift.trans (hadd.trans
    ((congrArg (fun b : ℝ => (S.circle (3 / 4 : ℝ)).decode ρ m y + b) hprod).trans
      ((returnCircle_product_reassemble
        (q := (S.circle (3 / 4 : ℝ)).decode ρ m y) hds).trans
        (returnCorrectionDisplacementLinear_apply S C (liftSectorParameter S C z) m θ ρ).symm)))

end ContinuousFlexibility.Statements
