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
  have ha := hN.returnFlowCircle_decode hS hT z hz m θ
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode
      (hN.returnFlowCircle hS hT z) m θ =
        C.minusFlow (liftSectorParameter S C z) m (C.right m) θ := by
    linarith only [ha]
  have hk := congrFun (hN.sectorReturnTransportCircle_odd_lift hS hT z hz m)
    (C.minusFlow (liftSectorParameter S C z) m (C.right m) θ)
  simp only [circleAffineLift, add_zero, one_mul] at hk
  unfold N01Properties.rightReturnChartCircle
  rw [map_add]
  simp only [Pi.add_apply]
  rw [circleShiftedChartComposeLinear_decode, heval]
  linarith only [ha, hk]

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
  let u := circleDerivativeLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.returnTransportInverseCircle hS hT z)
  let f : ℝ → ℝ := fun t => (S.circle (3 / 4 : ℝ)).decode u m (θ + t * d)
  have hG : ContDiff ℝ ∞ G := hN.returnTransportInverse_contDiff hS hT
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z) m
  have hf : Continuous f := (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 u).1 m).1.continuous.comp
    (continuous_const.add (continuous_id.mul continuous_const))
  have hi : (∫ t in (0 : ℝ)..1, deriv G (θ + t * d)) =
      1 + ∫ t in (0 : ℝ)..1, f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (1 + f t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hd := hN.returnTransportInverseCircle_derivative_decode hS hT z hz m (θ + t * d)
        change f t = deriv G (θ + t * d) - 1 at hd
        linarith only [hd]
      _ = _ := by
        rw [intervalIntegral.integral_add continuous_const.intervalIntegrable hf.intervalIntegrable,
          intervalIntegral.integral_const]
        simp only [sub_zero, one_smul]
  have hds := returnCorrection_dslope_integral (hG.of_le (by simp)) θ d
  have havg : (S.circle (3 / 4 : ℝ)).decode
      (hN.returnCorrectionDslopeCircle hS hT z) m θ = ∫ t in (0 : ℝ)..1, f t := by
    unfold N01Properties.returnCorrectionDslopeCircle
    rw [circleAverageComposeLinear_decode,
      hN.sectorReturnResidualCircle_decode hS hT z hz m θ]
    simp only [add_zero]
  change _ = dslope G θ (θ + d) - 1
  rw [havg, hds, hi]
  ring

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
  let y := rightChartCandidate S C (liftSectorParameter S C z) m
    (C.minusFlow (liftSectorParameter S C z) m (C.right m) θ)
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode
      (hN.rightReturnChartCircle hS hT z) m θ = y := by
    rw [hN.rightReturnChartCircle_decode hS hT z hz m θ]
    dsimp only [y]
    ring
  unfold N01Properties.returnCorrectionDisplacementCircleLinear
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    circleShiftedChartComposeLinear_decode, heval, map_add]
  simp only [Pi.add_apply]
  rw [circleProductBilinear_decode,
    hN.returnCorrectionDslopeCircle_decode hS hT z hz m y,
    returnCorrectionDisplacementLinear_apply]
  change (S.circle (3 / 4 : ℝ)).decode ρ m y +
    (dslope _ y (y + returnResidualField S C (liftSectorParameter S C z) m y) - 1) *
      (S.circle (3 / 4 : ℝ)).decode ρ m y =
    dslope _ y (y + returnResidualField S C (liftSectorParameter S C z) m y) *
      (S.circle (3 / 4 : ℝ)).decode ρ m y
  ring

end ContinuousFlexibility.Statements
