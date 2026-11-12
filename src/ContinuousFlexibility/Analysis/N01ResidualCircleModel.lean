import ContinuousFlexibility.Analysis.N01EndpointSmoothTame
import ContinuousFlexibility.Analysis.N01FlowSmallness
import ContinuousFlexibility.Analysis.N02ChartError
import ContinuousFlexibility.Analysis.CirclePositiveInverseModel

/-!
# The actual return residual as an element of the circle model

Write the return as theta - travel + a(theta). Composition with its
actual inverse sends leftChartPerturbation - a to the transported chart
perturbation u. Its odd part is the right chart perturbation, and inverse
composition of its even part is exactly the prescribed return residual.
Every operation takes place in the original physical circle model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01ResidualCircleModelStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology

section CircleModel

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleReturnTransport
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a l : S.Space) : S.Space :=
  circlePositiveInverseComposeLinear hS hT hD hγ (fun m => -travel m) a (l - a)

def circleReturnResidualModel
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a l : S.Space) : S.Space :=
  let u := circleReturnTransport hS hT hD hγ travel a l
  circlePositiveInverseComposeLinear hS hT hD hγ (fun _ => 0)
    (circleOddLinear hS u) (circleEvenLinear hS u)

theorem circleReturnTransport_decode_of_inverse
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a l : S.Space)
    (ha : a ∈ circlePositiveLiftDomain S) (g : ℕ → ℝ → ℝ)
    (hleft : ∀ m θ, g m (circleAffineLift (fun j => -travel j) (S.decode a) 1 m θ) = θ)
    (hright : ∀ m θ, circleAffineLift (fun j => -travel j) (S.decode a) 1 m (g m θ) = θ)
    (m : ℕ) (θ : ℝ) :
    θ + S.decode (circleReturnTransport hS hT hD hγ travel a l) m θ =
      g m θ + S.decode l m (g m θ) - travel m := by
  have hd := circlePositiveInverseComposeLinear_decode_of_leftInverse hS hT hD hγ
    (fun j => -travel j) a (l - a) ha g hleft m θ
  have heval : S.decode (l - a) m (g m θ) =
      S.decode l m (g m θ) - S.decode a m (g m θ) :=
    congrFun (congrFun (S.decode.map_sub l a) m) (g m θ)
  have hr := hright m θ
  simp only [circleAffineLift, one_mul] at hr
  change θ + S.decode
    (circlePositiveInverseComposeLinear hS hT hD hγ (fun j => -travel j) a (l - a)) m θ = _
  rw [hd, heval]
  linarith only [hr]

private theorem oddPart_id_add (f : ℝ → ℝ) (θ : ℝ) :
    oddPart (fun t => t + f t) θ = θ + oddPart f θ := by
  unfold oddPart
  ring

private theorem evenPart_id_add (f : ℝ → ℝ) (θ : ℝ) :
    evenPart (fun t => t + f t) θ = evenPart f θ := by
  unfold evenPart
  ring

end CircleModel

section ActualReturn

private theorem residualCircle_apply_zero_add
    {E F : Type*} [AddZeroClass E]
    (f : E → F) (a b : E) (ha : a = 0) :
    f (a + b) = f b := by
  exact congrArg f
    ((congrArg (fun u : E => u + b) ha).trans (zero_add b))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.right_radius_mem
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    C.right m ∈ Icc (C.left m) (C.right m) :=
  ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩

def N01Properties.returnFlowCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    (StateDirections S × ℝ) → CircleSpace S :=
  hN.endpointFlowCircle hS hT C.right hN.right_radius_mem

theorem N01Properties.returnFlowCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z) m θ =
      C.minusFlow (liftSectorParameter S C z) m (C.right m) θ - (θ - C.travel m) := by
  have href : C.minusFlow (C.referenceState, 0) m (C.right m) θ = θ - C.travel m :=
    (hN.minusFlow_reference_eq hS hT m (hN.right_radius_mem m) θ).trans
      (congrArg (fun t : ℝ => θ - t)
        (controlGeometry_travel_eq_radialTravel hN.2.2.2.1 m).symm)
  exact (hN.endpointFlowCircle_decode_apply hS hT C.right hN.right_radius_mem z hz m θ).trans
    (congrArg (fun t : ℝ => C.minusFlow (liftSectorParameter S C z) m (C.right m) θ - t) href)

theorem N01Properties.returnFlowCircle_lift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    circleAffineLift (fun j => -C.travel j)
        ((S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z)) 1 m =
      C.minusFlow (liftSectorParameter S C z) m (C.right m) := by
  funext θ
  have h := hN.returnFlowCircle_decode hS hT z hz m θ
  change θ + -C.travel m + 1 *
    (S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z) m θ = _
  linarith only [h]

theorem N01Properties.returnFlowCircle_positive
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.returnFlowCircle hS hT z ∈ circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ))
    (fun j => -C.travel j) (hN.returnFlowCircle hS hT z)).mpr
  intro m θ
  rw [hN.returnFlowCircle_lift hS hT z hz m]
  exact ((hN.2.2.2.2.2.2.1 (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m θ).2.2.2
      (C.right m) (hN.right_radius_mem m)).1

theorem referenceStateConditions.sector_leftChart
    (href : referenceStateConditions D S C) (z : StateDirections S × ℝ) (m : ℕ) (θ : ℝ) :
    stateLeftChart S (liftSectorParameter S C z).1 m θ =
      θ + (S.circle (3 / 4 : ℝ)).decode z.1.val.2.2.2 m θ := by
  change θ + (S.circle (3 / 4 : ℝ)).decode
    (C.referenceState.2.2.2 + z.1.val.2.2.2) m θ = _
  exact residualCircle_apply_zero_add
    (fun e : CircleSpace S => θ + (S.circle (3 / 4 : ℝ)).decode e m θ)
    C.referenceState.2.2.2 z.1.val.2.2.2 href.2.2.2.2.1

def N01Properties.sectorReturnTransportCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circleReturnTransport (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num : (0 : ℝ) < 3 / 4) C.travel (hN.returnFlowCircle hS hT z) z.1.val.2.2.2

theorem N01Properties.sectorReturnTransportCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    θ + (S.circle (3 / 4 : ℝ)).decode (hN.sectorReturnTransportCircle hS hT z) m θ =
      stateLeftChart S (liftSectorParameter S C z).1 m
        (C.minusReturnInverse (liftSectorParameter S C z) m θ) - C.travel m := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz (le_refl ε)
  have hs := hN.2.2.1.liftSectorParameter_sector z
  have hi := hN.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z) hz' hs
  have hl : ∀ j t, C.minusReturnInverse (liftSectorParameter S C z) j
      (circleAffineLift (fun i => -C.travel i)
        ((S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z)) 1 j t) = t := by
    intro j t
    exact (congrArg (C.minusReturnInverse (liftSectorParameter S C z) j)
      (congrFun (hN.returnFlowCircle_lift hS hT z hz j) t)).trans (hi j t).2.1
  have hr : ∀ j t, circleAffineLift (fun i => -C.travel i)
      ((S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z)) 1 j
        (C.minusReturnInverse (liftSectorParameter S C z) j t) = t := by
    intro j t
    exact (congrFun (hN.returnFlowCircle_lift hS hT z hz j)
      (C.minusReturnInverse (liftSectorParameter S C z) j t)).trans (hi j t).1
  have hd := circleReturnTransport_decode_of_inverse (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num : (0 : ℝ) < 3 / 4) C.travel (hN.returnFlowCircle hS hT z) z.1.val.2.2.2
    (hN.returnFlowCircle_positive hS hT z hz)
    (C.minusReturnInverse (liftSectorParameter S C z)) hl hr m θ
  exact hd.trans (congrArg (fun t : ℝ => t - C.travel m)
    (hN.2.2.1.sector_leftChart z m (C.minusReturnInverse (liftSectorParameter S C z) m θ)).symm)

theorem N01Properties.sectorReturnTransportCircle_odd_lift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    circleAffineLift (fun _ => 0)
      ((S.circle (3 / 4 : ℝ)).decode
        (circleOddLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z))) 1 m =
      rightChartCandidate S C (liftSectorParameter S C z) m := by
  let u := hN.sectorReturnTransportCircle hS hT z
  have hfun : (fun t => t + (S.circle (3 / 4 : ℝ)).decode u m t) =
      (fun t => stateLeftChart S (liftSectorParameter S C z).1 m
        (C.minusReturnInverse (liftSectorParameter S C z) m t) - C.travel m) :=
    funext (hN.sectorReturnTransportCircle_decode hS hT z hz m)
  funext θ
  simp only [circleAffineLift, add_zero, one_mul, circleOddLinear_decode]
  exact (oddPart_id_add ((S.circle (3 / 4 : ℝ)).decode u m) θ).symm.trans
    (congrFun (congrArg oddPart hfun) θ)

theorem N01Properties.sectorReturnTransportCircle_odd_positive
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    circleOddLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z) ∈
      circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mpr
  intro m θ
  rw [hN.sectorReturnTransportCircle_odd_lift hS hT z hz m]
  exact N01Properties.rightChart_deriv_pos S C (liftSectorParameter S C z) m hN
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) θ

theorem N01Properties.sectorReturnTransportCircle_even_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (circleEvenLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z)) m θ =
      evenPart (fun t => stateLeftChart S (liftSectorParameter S C z).1 m
        (C.minusReturnInverse (liftSectorParameter S C z) m t) - C.travel m) θ := by
  rw [circleEvenLinear_decode]
  have hfun := funext (hN.sectorReturnTransportCircle_decode hS hT z hz m)
  exact (evenPart_id_add
    ((S.circle (3 / 4 : ℝ)).decode (hN.sectorReturnTransportCircle hS hT z) m) θ).symm.trans
      (congrFun (congrArg evenPart hfun) θ)

def N01Properties.sectorReturnResidualCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circleReturnResidualModel (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num : (0 : ℝ) < 3 / 4) C.travel (hN.returnFlowCircle hS hT z) z.1.val.2.2.2

theorem N01Properties.sectorReturnResidualCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.sectorReturnResidualCircle hS hT z) m θ =
      returnResidualField S C (liftSectorParameter S C z) m θ := by
  let u := hN.sectorReturnTransportCircle hS hT z
  let k := circleOddLinear (hS.2.1 (3 / 4 : ℝ)) u
  have hk : k ∈ circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) :=
    hN.sectorReturnTransportCircle_odd_positive hS hT z hz
  have hi := hN.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z)
  have hleft : ∀ j t, C.rightChartInverse (liftSectorParameter S C z) j
      (circleAffineLift (fun _ => 0) ((S.circle (3 / 4 : ℝ)).decode k) 1 j t) = t := by
    intro j t
    exact (congrArg (C.rightChartInverse (liftSectorParameter S C z) j)
      (congrFun (hN.sectorReturnTransportCircle_odd_lift hS hT z hz j) t)).trans
        (hi j t).2.2.2
  have hd := circlePositiveInverseComposeLinear_decode_of_leftInverse
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num : (0 : ℝ) < 3 / 4)
    (fun _ => 0) k (circleEvenLinear (hS.2.1 (3 / 4 : ℝ)) u) hk
    (C.rightChartInverse (liftSectorParameter S C z)) hleft m θ
  exact hd.trans (hN.sectorReturnTransportCircle_even_decode hS hT z hz m
    (C.rightChartInverse (liftSectorParameter S C z) m θ))

end ActualReturn

end ContinuousFlexibility.Statements
