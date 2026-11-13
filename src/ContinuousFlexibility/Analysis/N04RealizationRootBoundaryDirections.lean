import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryPoint
import ContinuousFlexibility.Analysis.N01ReturnInverseCircle
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus
import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds

/-!
# Genuine directions of the actual inverse boundary point

Both root labels are the existing circle lifts: the left state chart or
the odd transported right chart. The existing positive-circle inverse
constructs their genuine joint inverses. The actual stored atlas point
is identified by its closed inverse identity, without choosing a smooth
parameter family of root charts.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04RootBoundaryDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Both genuine towers use the same original circle displacement and
unchanged joint sector and angular domain. The Boolean selector changes
only which existing root label is passed to circle inversion. -/
def n04Realization_rootLabel_jointDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    (SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        n01RootLabel S C (liftSectorParameter S C p.1) m side p.2)) ×
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        Function.invFun (n01RootLabel S C (liftSectorParameter S C p.1) m side) p.2) := by
  let H : CircleModelData := S.circle (3 / 4 : ℝ)
  have hH : IsCircleModel T (3 / 4 : ℝ) H := hS.2.1 (3 / 4 : ℝ)
  have hI : HasInterpolation H.grading := (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  let F : (StateDirections S × ℝ) → CircleSpace S := fun x =>
    if side then circleOddLinear hH (hN.sectorReturnTransportCircle hS hT x)
    else x.1.val.2.2.2
  let J : SmoothDirections U F := by
    cases side with
    | false =>
        exact (smoothDirectionsLinearOn (sectorChartContinuousLinear S) hU).congrOn
          (fun x _ => sectorChartContinuousLinear_apply S x)
    | true =>
        exact (solveSmoothDirectionsPostcomp
          (hN.smoothTameOn_sectorReturnTransportCircle hS hT).choose
          (circleOddContinuousLinear hH)).congrOn
            (fun x _ => circleOddContinuousLinear_apply hH
              (hN.sectorReturnTransportCircle hS hT x))
  have hlift (x : StateDirections S × ℝ) (hx : x ∈ U) (j : ℕ) :
      circleAffineLift (fun _ => 0) (H.decode (F x)) 1 j =
        n01RootLabel S C (liftSectorParameter S C x) j side := by
    cases side with
    | false =>
        funext θ
        simpa only [F, H, n01RootLabel, circleAffineLift, add_zero, one_mul,
          Bool.false_eq_true, ↓reduceIte] using
          (hN.2.2.1.sector_leftChart x j θ).symm
    | true => exact hN.sectorReturnTransportCircle_odd_lift hS hT x hx j
  have hpos : MapsTo F U (circlePositiveLiftDomain H) := by
    intro x hx
    cases side with
    | false =>
        apply (circlePositiveLiftDomain_iff hH (fun _ => 0) (F x)).mpr
        intro j θ
        rw [hlift x hx j]
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
          (hN.2.2.2.2.2.2.2.1 (liftSectorParameter S C x)
            (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
            (hN.2.2.1.liftSectorParameter_sector x) j θ).1
    | true => exact hN.sectorReturnTransportCircle_odd_positive hS hT x hx
  let G : (StateDirections S × ℝ) → CircleSpace S := fun x =>
    circlePositiveInversePerturbation hH hT hN.1.1 (by norm_num) (fun _ => 0) (F x)
  let JG : SmoothDirections U G :=
    circleInversePerturbationDirections hH hT hN.1.1 (by norm_num) hI
      (fun _ => 0) J hpos
  have hweight (j : ℕ) : 0 < T.H (T.sample j) :=
    (material_circle_sample_weights_pos hT hN.1.1).2 j
  refine ⟨?_, ?_⟩
  · apply (circleAffineLiftJointDirections hH hweight J (fun _ => 0) m).congrOn
    intro p hp
    simpa only [circleAffineLift, one_mul] using congrFun (hlift p.1 hp.1 m) p.2
  · apply (circleAffineLiftJointDirections hH hweight JG (fun _ => 0) m).congrOn
    intro p hp
    have hd : H.decode (G p.1) m p.2 =
        circleAffineInverse (fun _ => 0) (F p.1) m p.2 - (p.2 - 0) :=
      congrArg (fun g : ℕ → ℝ → ℝ => g m p.2)
        (circlePositiveInversePerturbation_decode hH hT hN.1.1 (by norm_num)
          (fun _ => 0) (F p.1) (hpos hp.1))
    have hinv : circleAffineInverse (fun _ => 0) (F p.1) m p.2 =
        Function.invFun (n01RootLabel S C (liftSectorParameter S C p.1) m side) p.2 :=
      congrArg (fun f : ℝ → ℝ => Function.invFun f p.2) (hlift p.1 hp.1 m)
    change p.2 + 0 + H.decode (G p.1) m p.2 = _
    linear_combination hd + hinv

/-- The original forward root label, with its genuine state and angle jets. -/
def n04Realization_rootLabel_forwardJointDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        n01RootLabel S C (liftSectorParameter S C p.1) m side p.2) :=
  (n04Realization_rootLabel_jointDirections hT hS hN m side).1

/-- The literal inverse of the same original root label. -/
def n04Realization_rootLabel_inverseJointDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        Function.invFun (n01RootLabel S C (liftSectorParameter S C p.1) m side) p.2) :=
  (n04Realization_rootLabel_jointDirections hT hS hN m side).2

/-- The returned genuine tower is for the literal current point of the
same typed atlas at its original physical root. No neighborhood is
shrunk and no root coordinate is selected again. -/
def n04Realization_actualRoot_currentPoint_jointDirections
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        canonicalCurrentPoint C K (liftSectorParameter S C p.1) k
          (if side then C.right m else C.left m, p.2)) := by
  let c : ℝ := if side then C.right m else C.left m
  let J := n04Realization_rootLabel_inverseJointDirections hT hS hN.1.1 m side
  have hpair : ContDiff ℝ ∞ (fun θ : ℝ => (c, θ)) :=
    contDiff_const.prodMk contDiff_id
  let JP := smoothDirections_contDiff_comp J isOpen_univ hpair.contDiffOn
    (fun _ _ => mem_univ _)
  apply JP.congrOn
  intro p hp
  change (c, Function.invFun
    (n01RootLabel S C (liftSectorParameter S C p.1) m side) p.2) = _
  exact (n04Realization_actualRoot_currentPoint_eq hT hS hN hfield e
    (liftSectorParameter_mem_stateNeighborhood hp.1 le_rfl)
    (hN.1.1.2.2.1.liftSectorParameter_sector p.1) k m side hi p.2).symm

end ContinuousFlexibility.Analysis
