import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelDirections
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections

/-!
# The actual forward root-label slope

Stored root-coordinate recursions use the forward label. Its circle is
the original chart coordinate at the left root and the odd actual return
transport at the right root. Both circles retain a common low order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04ControlledForwardLabelStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04PositiveGeometry_rootForwardCircle
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (side : Bool) :
    (StateDirections S × ℝ) → CircleSpace S := fun x =>
  if side then circleOddContinuousLinear (hS.2.1 (3 / 4 : ℝ))
    (hN.sectorReturnTransportCircle hS hT x)
  else sectorChartContinuousLinear S x

def n04PositiveGeometry_rootForwardCircle_directions
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (side : Bool) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (n04PositiveGeometry_rootForwardCircle hT hS hN side) := by
  cases side with
  | false =>
      exact smoothDirectionsLinearOn (sectorChartContinuousLinear S)
        (sectorNeighborhood_isOpen S base ε ε)
  | true =>
      exact solveSmoothDirectionsPostcomp
        (hN.smoothTameOn_sectorReturnTransportCircle hS hT).choose
        (circleOddContinuousLinear (hS.2.1 (3 / 4 : ℝ)))

theorem n04PositiveGeometry_rootForwardCircle_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (side : Bool) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (n04PositiveGeometry_rootForwardCircle hT hS hN side x) m θ =
      n01RootLabel S C (liftSectorParameter S C x) m side θ - θ := by
  have hlift : θ + (S.circle (3 / 4 : ℝ)).decode
      (n04PositiveGeometry_rootForwardCircle hT hS hN side x) m θ =
      n01RootLabel S C (liftSectorParameter S C x) m side θ := by
    cases side with
    | false =>
        simpa only [n04PositiveGeometry_rootForwardCircle, n01RootLabel,
          sectorChartContinuousLinear_apply, Bool.false_eq_true, ↓reduceIte] using
          (hN.2.2.1.sector_leftChart x m θ).symm
    | true =>
        simpa only [n04PositiveGeometry_rootForwardCircle, n01RootLabel,
          circleOddContinuousLinear_apply,
          ↓reduceIte, circleAffineLift, add_zero, one_mul] using
          congrFun (hN.sectorReturnTransportCircle_odd_lift hS hT x hx m) θ
  exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans hlift)

private theorem forwardCircle_fixedBaseBounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (side : Bool) :
    N04EndpointFixedBaseBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
      (n04PositiveGeometry_rootForwardCircle_directions hT hS hN side) := by
  cases side with
  | false =>
      change N04EndpointFixedBaseBounds (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading
        (smoothDirectionsLinearOn (sectorChartContinuousLinear S)
          (sectorNeighborhood_isOpen S base ε ε))
      apply n04PositiveGeometry_endpointBounds_linear
      intro s
      refine ⟨1, zero_le_one, fun x => ?_⟩
      simpa only [one_mul, sectorChartContinuousLinear_apply] using
        sectorParameter_chart_grading_le S s x
  | true =>
      let JT := (hN.smoothTameOn_sectorReturnTransportCircle hS hT).choose
      have hJT := n04PositiveGeometry_returnTransportCircle_fixedBaseBounds hT hS hN hflow JT
      change N04EndpointFixedBaseBounds (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading
        (solveSmoothDirectionsPostcomp JT (circleOddContinuousLinear (hS.2.1 (3 / 4 : ℝ))))
      apply hJT.postLinear (circleOddContinuousLinear (hS.2.1 (3 / 4 : ℝ))) 0
      intro s
      obtain ⟨A, hA⟩ := circleOddLinear_tame (hS.2.1 (3 / 4 : ℝ)) s (Nat.zero_le s)
      exact ⟨A, A.coe_nonneg, fun y => hA y⟩

theorem n04PositiveGeometry_rootForwardDefect_fixedBase_oneHigh_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ b : ℕ, b ≤ s → ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun x => iteratedDeriv b (fun α =>
            n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading B x ≤ R →
        ∀ v : Fin n → (StateDirections S × ℝ),
          |J.D n x v| ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            tameJetSize (pairGrading (sectorGrading S) realGrading) n s ell B x v := by
  let JC := n04PositiveGeometry_rootForwardCircle_directions hT hS hN
  have hpair := (forwardCircle_fixedBaseBounds hT hS hN hflow false).prod
    (sectorPairGrading_monotone S) (forwardCircle_fixedBaseBounds hT hS hN hflow true)
  refine hpair.elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro ell hell
  refine ⟨ell + 1, fun R hR s => ?_⟩
  refine (hell R hR (s + 1)).elim ?_
  intro K hK
  refine ⟨2 * circleSobolevConstant * K,
    mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hK.1, ?_⟩
  intro b hbside side m θ J x hx hxR v
  have hside : (S.circle (3 / 4 : ℝ)).grading (s + 1) ((JC side).D n x v) ≤
      K * tameJetSize (pairGrading (sectorGrading S) realGrading) n (s + 1) ell B x v := by
    have hp := hK.2 x hx hxR v
    change (S.circle (3 / 4 : ℝ)).grading (s + 1) ((JC false).D n x v) +
      (S.circle (3 / 4 : ℝ)).grading (s + 1) ((JC true).D n x v) ≤ _ at hp
    cases side with
    | false => exact (le_add_of_nonneg_right (apply_nonneg _ _)).trans hp
    | true => exact (le_add_of_nonneg_left (apply_nonneg _ _)).trans hp
  let J' : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => iteratedDeriv b ((S.circle (3 / 4 : ℝ)).decode
        (n04PositiveGeometry_rootForwardCircle hT hS hN side y) m) θ) :=
    J.congrOn (fun y hy => congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
      (funext (fun α => (n04PositiveGeometry_rootForwardCircle_decode
        hT hS hN hy side m α).symm)))
  exact n04PositiveGeometry_endpointBounds_angleEvaluation (hS.2.1 (3 / 4 : ℝ))
    (material_circle_sample_weights_pos hT hN.1.1).2
    (pairGrading (sectorGrading S) realGrading) (JC side) hx v hside b hbside m θ J'

def n04PositiveGeometry_rootForwardDefect_angularDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (side : Bool) (m b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv b (fun α =>
        n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ) :=
  (circleDecodedAngularDirections (hS.2.1 (3 / 4 : ℝ))
    (n04PositiveGeometry_rootForwardCircle_directions hT hS hN side) b m θ).congrOn
      (fun x hx => congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
        (funext (fun α => n04PositiveGeometry_rootForwardCircle_decode hT hS hN hx side m α)))

private theorem forward_slope_add_identity
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (deriv (fun α => f α + α)) θ =
      iteratedDeriv (n + 1) f θ + if n = 0 then 1 else 0 := by
  rw [← iteratedDeriv_succ']
  have hadd : iteratedDeriv (n + 1) (fun α => f α + α) θ =
      iteratedDeriv (n + 1) f θ + iteratedDeriv (n + 1) (id : ℝ → ℝ) θ :=
    iteratedDeriv_fun_add (f := f) (g := fun α : ℝ => α) (n := n + 1)
      (hf.contDiffAt.of_le (by simp)) contDiffAt_id
  have hid : iteratedDeriv (n + 1) (id : ℝ → ℝ) θ = if n = 0 then 1 else 0 := by
    rw [iteratedDeriv_id, if_neg (Nat.succ_ne_zero n)]
    by_cases hn : n = 0
    · subst n
      norm_num
    · rw [if_neg (by omega : n + 1 ≠ 1), if_neg hn]
  exact hadd.trans (congrArg (fun t : ℝ => iteratedDeriv (n + 1) f θ + t) hid)

theorem n04PositiveGeometry_rootForwardDerivative_angular_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (side : Bool) (m b : ℕ) (θ : ℝ) :
    iteratedDeriv b (deriv (n01RootLabel S C (liftSectorParameter S C x) m side)) θ =
      iteratedDeriv (b + 1) (fun α =>
        n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ +
        if b = 0 then 1 else 0 := by
  let f : ℝ → ℝ := (S.circle (3 / 4 : ℝ)).decode
    (n04PositiveGeometry_rootForwardCircle hT hS hN side x) m
  have hf : ContDiff ℝ ∞ f := by
    simpa only [iteratedDeriv_zero] using circleDecoded_iteratedDeriv_contDiff
      (hS.2.1 (3 / 4 : ℝ)) (n04PositiveGeometry_rootForwardCircle hT hS hN side x) m 0
  have hdefect : f = (fun α =>
      n01RootLabel S C (liftSectorParameter S C x) m side α - α) :=
    funext (fun α => n04PositiveGeometry_rootForwardCircle_decode hT hS hN hx side m α)
  have hfull : n01RootLabel S C (liftSectorParameter S C x) m side = (fun α => f α + α) := by
    funext α
    exact (sub_add_cancel _ α).symm.trans
      (congrArg (fun t : ℝ => t + α) (congrFun hdefect α).symm)
  calc
    _ = iteratedDeriv b (deriv (fun α => f α + α)) θ :=
      congrArg (fun g : ℝ → ℝ => iteratedDeriv b (deriv g) θ) hfull
    _ = iteratedDeriv (b + 1) f θ + if b = 0 then 1 else 0 :=
      forward_slope_add_identity hf b θ
    _ = _ := congrArg (fun g : ℝ → ℝ =>
      iteratedDeriv (b + 1) g θ + if b = 0 then 1 else 0) hdefect

theorem n04PositiveGeometry_rootForwardDerivative_positive_jet_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (side : Bool) (m b : ℕ) (θ : ℝ)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv b (deriv (n01RootLabel S C (liftSectorParameter S C x) m side)) θ))
    (K : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
      iteratedDeriv (b + 1) (fun α =>
        n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ))
    {k : ℕ} (hk : 0 < k) {x : StateDirections S × ℝ}
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin k → (StateDirections S × ℝ)) :
    J.D k x v = K.D k x v := by
  let K' := K.congrOn (fun y hy => (eq_sub_iff_add_eq).mpr
    (n04PositiveGeometry_rootForwardDerivative_angular_eq hT hS hN hy side m b θ).symm)
  exact (smoothDirections_D_sub_constant J K' hk hx v).symm

end ContinuousFlexibility.Analysis
