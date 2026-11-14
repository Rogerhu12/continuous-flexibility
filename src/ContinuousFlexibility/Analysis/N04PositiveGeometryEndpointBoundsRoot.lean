module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsLeft
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRight
public import ContinuousFlexibility.Analysis.CanonicalNeighborhoodRestriction

/-!
# Both actual inverse root labels on one common neighborhood

The two existing circle maps are paired before any parameter order is
chosen. The resulting bound has constants independent of the Boolean
endpoint selector, component and angle. The final theorem obtains its
ordinary-flow Jacobian hypothesis from N01 on one smaller neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04PositiveEndpointBoundsRootStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The existing inverse circle at either original root. -/
def n04PositiveGeometry_rootInverseCircle
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (side : Bool) :
    (StateDirections S × ℝ) → CircleSpace S :=
  if side then hN.rightChartInverseCircle hS hT
  else n04PositiveGeometry_leftRootInverseCircle hT hS hN

def n04PositiveGeometry_rootInverseCircle_directions
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (side : Bool) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (n04PositiveGeometry_rootInverseCircle hT hS hN side) := by
  cases side with
  | false => exact n04PositiveGeometry_leftRootInverseCircle_directions hT hS hN
  | true => exact (hN.smoothTameOn_rightChartInverseCircle hS hT).choose

theorem n04PositiveGeometry_rootInverseCircle_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (side : Bool) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (n04PositiveGeometry_rootInverseCircle hT hS hN side x) m θ =
      Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) θ - θ := by
  cases side with
  | false => exact n04PositiveGeometry_leftRootInverseCircle_decode hT hS hN hx m θ
  | true =>
      let e := circleOddLinear (hS.2.1 (3 / 4 : ℝ))
        (hN.sectorReturnTransportCircle hS hT x)
      have hd := congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
        (circlePositiveInversePerturbation_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
          (by norm_num) (fun _ => 0) e
          (hN.sectorReturnTransportCircle_odd_positive hS hT x hx))
      have hi : circleAffineInverse (fun _ => 0) e m θ =
          Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m true) θ :=
        congrArg (fun f : ℝ → ℝ => Function.invFun f θ)
          (hN.sectorReturnTransportCircle_odd_lift hS hT x hx m)
      exact hd.trans (congrArg₂ (fun r t : ℝ => r - t) hi (sub_zero θ))

private theorem leftRootInverseCircle_fixedBaseBounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    N04EndpointFixedBaseBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
      (n04PositiveGeometry_rootInverseCircle_directions hT hS hN false) := by
  refine (n04PositiveGeometry_leftRootInverseCircle_fixedBase_oneHigh hT hS hN).elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro ell hell
  refine ⟨ell, fun R _ s => ?_⟩
  refine (hell (max 1 R) (le_max_left _ _) s).elim ?_
  intro K hK
  exact ⟨K, hK.1, fun x hx hxR v =>
    hK.2 (n04PositiveGeometry_rootInverseCircle_directions hT hS hN false)
      x hx (hxR.trans (le_max_right _ _)) v⟩

/-- A uniform estimate for every genuine scalar tower of either literal
inverse-root-label displacement. All constants precede the side,
component and angle. -/
theorem n04PositiveGeometry_rootInverseDefect_fixedBase_oneHigh_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ b : ℕ, b ≤ s → ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun x => iteratedDeriv b (fun α =>
            Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading B x ≤ R →
        ∀ v : Fin n → (StateDirections S × ℝ),
          |J.D n x v| ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            tameJetSize (pairGrading (sectorGrading S) realGrading) n s ell B x v := by
  let JC := n04PositiveGeometry_rootInverseCircle_directions hT hS hN
  have hleft := leftRootInverseCircle_fixedBaseBounds hT hS hN
  have hright := n04PositiveGeometry_rightRootInverseCircle_fixedBaseBounds
    hT hS hN hflow (JC true)
  have hpair := hleft.prod (sectorPairGrading_monotone S) hright
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
  intro b hb side m θ J x hx hxR v
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
        (n04PositiveGeometry_rootInverseCircle hT hS hN side y) m) θ) :=
    J.congrOn (fun y hy =>
      congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
        (funext (fun α =>
          (n04PositiveGeometry_rootInverseCircle_decode hT hS hN hy side m α).symm)))
  exact n04PositiveGeometry_endpointBounds_angleEvaluation (hS.2.1 (3 / 4 : ℝ))
    (material_circle_sample_weights_pos hT hN.1.1).2
    (pairGrading (sectorGrading S) realGrading) (JC side) hx v hside b hb m θ J'

/-- N01 itself supplies the common smaller neighborhood. This final
endpoint estimate assumes no flow or inverse-jet bounds. -/
theorem n04PositiveGeometry_rootInverseDefect_fixedBase_oneHigh
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 0 ≤ R →
        ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
          ∀ b : ℕ, b ≤ s → ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
          ∀ J : SmoothDirections (sectorNeighborhood S newBase ε' ε')
            (fun x => iteratedDeriv b (fun α =>
              Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m side) α - α) θ),
          ∀ x ∈ sectorNeighborhood S newBase ε' ε',
            pairGrading (sectorGrading S) realGrading B x ≤ R →
          ∀ v : Fin n → (StateDirections S × ℝ),
            |J.D n x v| ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
              tameJetSize (pairGrading (sectorGrading S) realGrading) n s ell B x v := by
  refine (exists_ordinaryFlowJacobianBounds_of_n01 hT hN).elim ?_
  intro newBase hB
  refine hB.elim ?_
  intro ε' he
  have hN' := n01Properties_restrict hT hN he.1 le_rfl he.2.1 he.2.2.1
  exact ⟨newBase, ε', he.1, he.2.1, he.2.2.1,
    n04PositiveGeometry_rootInverseDefect_fixedBase_oneHigh_of_flow hT hS hN' he.2.2.2⟩

end ContinuousFlexibility.Analysis
