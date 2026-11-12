import ContinuousFlexibility.Analysis.N01SelectorInverse
import ContinuousFlexibility.Analysis.N01ResidualSmoothTame
import ContinuousFlexibility.Analysis.CircleCompositionSmoothTame
import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity

/-!
# Actual inverse return coordinates and the initial correction in the circle model

The inverse right chart is the positive inverse of the odd transported
chart. Composing it with the actual inverse return gives the coordinate
used in the divided difference. A final composition with the actual
left chart gives precisely the initial correction map. These are
elements of the supplied circle space, with the full smooth tame
towers inherited from the actual forward flow and inverse composition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

theorem smoothTameOn_circleShiftedChartCompose_maps
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation H.grading) (travel : ℕ → ℝ)
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (ht : WithSeminorms p)
    {U : Set E} (hU : IsOpen U) {f g : E → H.Space}
    (hf : SmoothTameOn p H.grading U f) (hg : SmoothTameOn p H.grading U g) :
    SmoothTameOn p H.grading U
      (fun x => circleShiftedChartComposeLinear hH hT hD hγ travel (f x) (g x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  exact smoothTameOn_comp_topological hp ht (withSeminorms_pairGrading htop htop)
    hU isOpen_univ (fun _ _ => mem_univ _)
    (smoothTameOn_prodMk hp ht hf hg)
    (smoothTameOn_circleShiftedChartComposeLinear hH hT hD hγ hi travel)

local instance n01ReturnInverseCircleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def N01Properties.rightChartInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun _ => 0)
    (circleOddLinear (hS.2.1 (3 / 4 : ℝ)) (hN.sectorReturnTransportCircle hS hT z))

theorem N01Properties.rightChartInverseCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.rightChartInverseCircle hS hT z) m θ =
      C.rightChartInverse (liftSectorParameter S C z) m θ - θ := by
  let k := circleOddLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.sectorReturnTransportCircle hS hT z)
  have hi := hN.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z)
  have hleft : ∀ j t, C.rightChartInverse (liftSectorParameter S C z) j
      (circleAffineLift (fun _ => 0) ((S.circle (3 / 4 : ℝ)).decode k) 1 j t) = t := by
    intro j t
    exact (congrArg (C.rightChartInverse (liftSectorParameter S C z) j)
      (congrFun (hN.sectorReturnTransportCircle_odd_lift hS hT z hz j) t)).trans
        (hi j t).2.2.2
  have hd := congrFun (congrFun (circlePositiveInversePerturbation_decode
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0) k
    (hN.sectorReturnTransportCircle_odd_positive hS hT z hz)) m) θ
  have hinv := circleAffineInverse_eq_of_leftInverse
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num) (fun _ => 0) k
    (C.rightChartInverse (liftSectorParameter S C z)) hleft m θ
  exact hd.trans (by rw [hinv, sub_zero])

theorem N01Properties.smoothTameOn_rightChartInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.rightChartInverseCircle hS hT) := by
  let H := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  have hp := sectorPairGrading_monotone S
  have ht := sectorPairGrading_withSeminorms S
  have htop : WithSeminorms H.grading :=
    withSeminorms_graded (fun n => H.level n) H.bond
  have hU := sectorNeighborhood_isOpen S base ε ε
  have hi : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  have hk : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => circleOddLinear hH (hN.sectorReturnTransportCircle hS hT z)) :=
    smoothTameOn_comp_topological hp ht htop hU isOpen_univ (fun _ _ => mem_univ _)
      (hN.smoothTameOn_sectorReturnTransportCircle hS hT)
      (smoothTameOn_circleOddLinear hH)
  exact smoothTameOn_comp_topological hp ht htop hU
    (circlePositiveLiftDomain_isOpen hH hT hN.1.1 (by norm_num))
    (fun z hz => hN.sectorReturnTransportCircle_odd_positive hS hT z hz) hk
    (smoothTameOn_circlePositiveInversePerturbation hH hT hN.1.1 (by norm_num) hi
      (fun _ => 0))

theorem N01Properties.selectorInverseCircle_right_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        (hN.selectorInverseCircle hS hT C.right hN.right_radius_mem z) m θ =
      C.minusReturnInverse (liftSectorParameter S C z) m θ - (θ + C.travel m) := by
  have hi := hN.2.2.2.2.2.2.2.2.1 (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z)
  have hleft : ∀ j t, C.minusReturnInverse (liftSectorParameter S C z) j
      (circleAffineLift (fun i => -C.travel i)
        ((S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z)) 1 j t) = t := by
    intro j t
    exact (congrArg (C.minusReturnInverse (liftSectorParameter S C z) j)
      (congrFun (hN.returnFlowCircle_lift hS hT z hz j) t)).trans (hi j t).2.1
  have hinv := circleAffineInverse_eq_of_leftInverse
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (fun i => -C.travel i) (hN.returnFlowCircle hS hT z)
    (C.minusReturnInverse (liftSectorParameter S C z)) hleft m θ
  change Function.invFun (circleAffineLift (fun i => -C.travel i)
    ((S.circle (3 / 4 : ℝ)).decode (hN.returnFlowCircle hS hT z)) 1 m) θ = _ at hinv
  rw [hN.returnFlowCircle_lift hS hT z hz m] at hinv
  rw [hN.selectorInverseCircle_decode hS hT C.right hN.right_radius_mem z hz,
    hinv, ← controlGeometry_travel_eq_radialTravel hN.2.2.2.1 m]

/-- The displacement of the exact inverse coordinate in the correction's
divided difference, relative to its fixed optical translation. -/
def N01Properties.returnTransportInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  hN.rightChartInverseCircle hS hT z +
    circleShiftedChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun _ => 0) (hN.rightChartInverseCircle hS hT z)
      (hN.selectorInverseCircle hS hT C.right hN.right_radius_mem z)

theorem N01Properties.returnTransportInverseCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.returnTransportInverseCircle hS hT z) m θ =
      C.minusReturnInverse (liftSectorParameter S C z) m
        (C.rightChartInverse (liftSectorParameter S C z) m θ) - (θ + C.travel m) := by
  have heval : θ + 0 + (S.circle (3 / 4 : ℝ)).decode
      (hN.rightChartInverseCircle hS hT z) m θ =
        C.rightChartInverse (liftSectorParameter S C z) m θ := by
    rw [hN.rightChartInverseCircle_decode hS hT z hz m θ]
    ring
  unfold N01Properties.returnTransportInverseCircle
  rw [map_add]
  simp only [Pi.add_apply]
  rw [circleShiftedChartComposeLinear_decode, heval,
    hN.selectorInverseCircle_right_decode hS hT z hz,
    hN.rightChartInverseCircle_decode hS hT z hz]
  ring

theorem N01Properties.smoothTameOn_returnTransportInverseCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.returnTransportInverseCircle hS hT) := by
  have hright := hN.smoothTameOn_rightChartInverseCircle hS hT
  have hflow := hN.smoothTameOn_selectorInverseCircle hS hT C.right hN.right_radius_mem
  have hcomp := smoothTameOn_circleShiftedChartCompose_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0)
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (sectorNeighborhood_isOpen S base ε ε) hright hflow
  exact smoothTameOn_add (sectorPairGrading_monotone S) hright hcomp

/-- The actual initial correction minus the identity, in the original
circle space. Its two compositions use the prescribed inverse maps. -/
def N01Properties.returnCorrectionInitialCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) : CircleSpace S :=
  z.1.val.2.2.2 +
    circleShiftedChartComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
      (fun m => -C.travel m) z.1.val.2.2.2 (hN.returnTransportInverseCircle hS hT z)

theorem N01Properties.returnCorrectionInitialCircle_decode
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (hN.returnCorrectionInitialCircle hS hT z) m θ =
      returnCorrectionInitialMap S C (liftSectorParameter S C z) m θ - θ := by
  have hl := hN.2.2.1.sector_leftChart z m θ
  have heval : θ + -C.travel m + (S.circle (3 / 4 : ℝ)).decode z.1.val.2.2.2 m θ =
      stateLeftChart S (liftSectorParameter S C z).1 m θ - C.travel m := by
    rw [hl]
    ring
  unfold N01Properties.returnCorrectionInitialCircle
  rw [map_add]
  simp only [Pi.add_apply]
  rw [circleShiftedChartComposeLinear_decode, heval,
    hN.returnTransportInverseCircle_decode hS hT z hz,
    returnCorrectionInitialMap_apply]
  rw [hl]
  ring

theorem N01Properties.returnCorrectionInitialCircle_lift
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) :
    circleAffineLift (fun _ => 0)
      ((S.circle (3 / 4 : ℝ)).decode (hN.returnCorrectionInitialCircle hS hT z)) 1 m =
        returnCorrectionInitialMap S C (liftSectorParameter S C z) m := by
  funext θ
  simp only [circleAffineLift, add_zero, one_mul,
    hN.returnCorrectionInitialCircle_decode hS hT z hz m θ]
  ring

theorem N01Properties.returnCorrectionInitialCircle_positive
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    hN.returnCorrectionInitialCircle hS hT z ∈ circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) := by
  apply (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mpr
  intro m θ
  rw [hN.returnCorrectionInitialCircle_lift hS hT z hz m]
  exact hN.returnCorrectionInitialMap_deriv_pos
    (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
    (hN.2.2.1.liftSectorParameter_sector z) m θ

theorem N01Properties.smoothTameOn_returnCorrectionInitialCircle
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (hN.returnCorrectionInitialCircle hS hT) := by
  have hchart : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ => z.1.val.2.2.2) :=
    smoothTameOn_restrict_open (smoothTameOn_sectorChart S)
      (sectorNeighborhood_isOpen S base ε ε) (subset_univ _)
  have hcomp := smoothTameOn_circleShiftedChartCompose_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun m => -C.travel m)
    (sectorPairGrading_monotone S) (sectorPairGrading_withSeminorms S)
    (sectorNeighborhood_isOpen S base ε ε) hchart
    (hN.smoothTameOn_returnTransportInverseCircle hS hT)
  exact smoothTameOn_add (sectorPairGrading_monotone S) hchart hcomp

end ContinuousFlexibility.Statements
