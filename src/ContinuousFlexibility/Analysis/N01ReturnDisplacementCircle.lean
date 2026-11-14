module

public import ContinuousFlexibility.Analysis.N01ReturnInverseCircle
public import ContinuousFlexibility.Analysis.CircleAveragedComposition
public import ContinuousFlexibility.Analysis.CircleWeightedProduct
public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualLinear

/-!
# The actual independent-residual displacement as a circle linear map

The removable divided difference is evaluated by its true derivative
integral. The affine part of the inverse contributes one, and the
remaining integral is the existing averaged composition of a decoded
circle derivative. Multiplication and the actual forward return chart
then realize exactly the original displacement linear map, including
at zeros of the residual.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01ReturnDisplacementCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff

private theorem returnDisplacement_shift_argument (θ t y d : ℝ)
    (hd : d = y - (θ - t)) : θ + -t + d = y := by
  linarith only [hd]

private theorem returnDisplacement_compose (θ t r y a b : ℝ)
    (ha : a = r - (θ - t)) (hb : r + 0 + 1 * b = y) :
    a + b = y - (θ - t) := by
  linarith only [ha, hb]

private theorem returnDisplacement_integral_one_add (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, 1 + f t) = 1 + ∫ t in (0 : ℝ)..1, f t := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using
    (intervalIntegral.integral_add h1 (hf.intervalIntegrable 0 1))

private theorem returnDisplacement_average_zero (u : ℝ → ℝ) (θ e d : ℝ)
    (he : e = d) :
    (∫ t in (0 : ℝ)..1, u (θ + 0 + t * e)) =
      ∫ t in (0 : ℝ)..1, u (θ + t * d) := by
  rw [he]
  simp only [add_zero]

private theorem returnDisplacement_sub_one (I A : ℝ) (hA : A = 1 + I) :
    I = A - 1 := by
  linarith only [hA]

private theorem returnDisplacement_scaled_correction (a u : ℝ) :
    u + (a - 1) * u = a * u := by
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
  let a : CircleSpace S := hN.returnFlowCircle hS hT z
  let k : CircleSpace S := circleOddLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.sectorReturnTransportCircle hS hT z)
  let q : CircleSpace S := circleShiftedChartComposeLinear
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun j => -C.travel j) a k
  let r : ℝ := C.minusFlow (liftSectorParameter S C z) m (C.right m) θ
  let y : ℝ := rightChartCandidate S C (liftSectorParameter S C z) m r
  have ha : (S.circle (3 / 4 : ℝ)).decode a m θ = r - (θ - C.travel m) :=
    hN.returnFlowCircle_decode hS hT z hz m θ
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode a m θ = r :=
    returnDisplacement_shift_argument θ (C.travel m) r
      ((S.circle (3 / 4 : ℝ)).decode a m θ) ha
  have hk : r + 0 + 1 * (S.circle (3 / 4 : ℝ)).decode k m r = y :=
    congrFun (hN.sectorReturnTransportCircle_odd_lift hS hT z hz m) r
  have hq : (S.circle (3 / 4 : ℝ)).decode q m θ =
      (S.circle (3 / 4 : ℝ)).decode k m r :=
    (circleShiftedChartComposeLinear_decode
      (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun j => -C.travel j) a k m θ).trans
        (congrArg (fun s : ℝ => (S.circle (3 / 4 : ℝ)).decode k m s) heval)
  have hadd : (S.circle (3 / 4 : ℝ)).decode (hN.rightReturnChartCircle hS hT z) m θ =
      (S.circle (3 / 4 : ℝ)).decode a m θ + (S.circle (3 / 4 : ℝ)).decode q m θ :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m θ) ((S.circle (3 / 4 : ℝ)).decode.map_add a q)
  exact hadd.trans ((congrArg (fun b : ℝ => (S.circle (3 / 4 : ℝ)).decode a m θ + b) hq).trans
    (returnDisplacement_compose θ (C.travel m) r y
      ((S.circle (3 / 4 : ℝ)).decode a m θ)
      ((S.circle (3 / 4 : ℝ)).decode k m r) ha hk))

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
  have hi : (∫ t in (0 : ℝ)..1, deriv G (θ + t * d)) =
      1 + ∫ t in (0 : ℝ)..1, f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (1 + f t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hd := hN.returnTransportInverseCircle_derivative_decode hS hT z hz m (θ + t * d)
        change f t = deriv G (θ + t * d) - 1 at hd
        linarith only [hd]
      _ = _ := returnDisplacement_integral_one_add f hf
  have hds := returnCorrection_dslope_integral (hG.of_le (by simp)) θ d
  have havg : (S.circle (3 / 4 : ℝ)).decode
      (hN.returnCorrectionDslopeCircle hS hT z) m θ = ∫ t in (0 : ℝ)..1, f t := by
    let e : CircleSpace S := hN.sectorReturnResidualCircle hS hT z
    have he : (S.circle (3 / 4 : ℝ)).decode e m θ = d :=
      hN.sectorReturnResidualCircle_decode hS hT z hz m θ
    have hdecode : (S.circle (3 / 4 : ℝ)).decode
        (hN.returnCorrectionDslopeCircle hS hT z) m θ =
          ∫ t in (0 : ℝ)..1, (S.circle (3 / 4 : ℝ)).decode u m
            (θ + 0 + t * (S.circle (3 / 4 : ℝ)).decode e m θ) :=
      circleAverageComposeLinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
        (by norm_num) (fun _ => 0) e u m θ
    exact hdecode.trans (returnDisplacement_average_zero
      ((S.circle (3 / 4 : ℝ)).decode u m) θ
      ((S.circle (3 / 4 : ℝ)).decode e m θ) d he)
  exact havg.trans (returnDisplacement_sub_one (∫ t in (0 : ℝ)..1, f t)
    (dslope G θ (θ + d)) (hds.trans hi))

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
  let G : ℝ → ℝ := fun t => C.minusReturnInverse (liftSectorParameter S C z) m
    (C.rightChartInverse (liftSectorParameter S C z) m t)
  let slope : ℝ := dslope G y (y + returnResidualField S C (liftSectorParameter S C z) m y)
  let e : CircleSpace S := hN.rightReturnChartCircle hS hT z
  let d : CircleSpace S := hN.returnCorrectionDslopeCircle hS hT z
  let b : CircleSpace S :=
    circleProductBilinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) d ρ
  let u : CircleSpace S := ρ + b
  have he : (S.circle (3 / 4 : ℝ)).decode e m θ = y - (θ - C.travel m) :=
    hN.rightReturnChartCircle_decode hS hT z hz m θ
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode
      e m θ = y :=
    returnDisplacement_shift_argument θ (C.travel m) y
      ((S.circle (3 / 4 : ℝ)).decode e m θ) he
  have hcomp : (S.circle (3 / 4 : ℝ)).decode
      (hN.returnCorrectionDisplacementCircleLinear hS hT z ρ) m θ =
        (S.circle (3 / 4 : ℝ)).decode u m y :=
    (circleShiftedChartComposeLinear_decode
      (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun j => -C.travel j) e u m θ).trans
        (congrArg (fun t : ℝ => (S.circle (3 / 4 : ℝ)).decode u m t) heval)
  have hcoef : (S.circle (3 / 4 : ℝ)).decode d m y = slope - 1 :=
    hN.returnCorrectionDslopeCircle_decode hS hT z hz m y
  have hb : (S.circle (3 / 4 : ℝ)).decode b m y =
      (slope - 1) * (S.circle (3 / 4 : ℝ)).decode ρ m y :=
    (congrArg (fun f : ℕ → ℝ → ℝ => f m y)
      (circleProductBilinear_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
        (by norm_num) d ρ)).trans
          (congrArg (fun a : ℝ => a * (S.circle (3 / 4 : ℝ)).decode ρ m y) hcoef)
  have hadd : (S.circle (3 / 4 : ℝ)).decode u m y =
      (S.circle (3 / 4 : ℝ)).decode ρ m y + (S.circle (3 / 4 : ℝ)).decode b m y :=
    congrArg (fun f : ℕ → ℝ → ℝ => f m y) ((S.circle (3 / 4 : ℝ)).decode.map_add ρ b)
  have hscaled : (S.circle (3 / 4 : ℝ)).decode u m y =
      slope * (S.circle (3 / 4 : ℝ)).decode ρ m y :=
    hadd.trans ((congrArg (fun a : ℝ => (S.circle (3 / 4 : ℝ)).decode ρ m y + a) hb).trans
      (returnDisplacement_scaled_correction slope ((S.circle (3 / 4 : ℝ)).decode ρ m y)))
  have htarget : returnCorrectionDisplacementLinear S C (liftSectorParameter S C z) m θ ρ =
      slope * (S.circle (3 / 4 : ℝ)).decode ρ m y :=
    returnCorrectionDisplacementLinear_apply S C (liftSectorParameter S C z) m θ ρ
  exact hcomp.trans (hscaled.trans htarget.symm)

end ContinuousFlexibility.Statements
