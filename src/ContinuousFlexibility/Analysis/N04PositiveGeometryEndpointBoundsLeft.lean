import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsEvaluation
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections

/-!
# Fixed-base one-high estimates for the actual left-root inverse

The original left root label is the affine circle lift of the sector's
chart coordinate. Its N01 derivative lower bound therefore feeds the
genuine positive inverse estimate directly. Every angular derivative of
the literal inverse-label displacement has the same low parameter order
and its original sampled height weight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

local instance n04PositiveEndpointBoundsLeftStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem leftRootChart_lift
    (hN : N01Properties D T S C base loss ε)
    (x : StateDirections S × ℝ) (m : ℕ) :
    circleAffineLift (fun _ => 0)
      ((S.circle (3 / 4 : ℝ)).decode (sectorChartContinuousLinear S x)) 1 m =
      n01RootLabel S C (liftSectorParameter S C x) m false := by
  funext θ
  simpa only [n01RootLabel, circleAffineLift, sectorChartContinuousLinear_apply,
    add_zero, one_mul, Bool.false_eq_true, ↓reduceIte] using
      (hN.2.2.1.sector_leftChart x m θ).symm

private theorem leftRootChart_lower
    (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    1 / 2 ≤ deriv (circleAffineLift (fun _ => 0)
      ((S.circle (3 / 4 : ℝ)).decode (sectorChartContinuousLinear S x)) 1 m) θ := by
  have hb := (hN.2.2.2.2.2.2.2.1 (liftSectorParameter S C x)
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) m θ).1
  exact hb.trans_eq (congrArg (fun f : ℝ → ℝ => deriv f θ)
    (leftRootChart_lift hN x m)).symm

private theorem leftRootChart_positive
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε) :
    sectorChartContinuousLinear S x ∈ circlePositiveLiftDomain (S.circle (3 / 4 : ℝ)) :=
  (circlePositiveLiftDomain_iff (hS.2.1 (3 / 4 : ℝ)) (fun _ => 0) _).mpr
    (fun m θ => (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (leftRootChart_lower hN hx m θ))

/-- The actual circle displacement of the original left-root inverse. -/
def n04PositiveGeometry_leftRootInverseCircle
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (x : StateDirections S × ℝ) : CircleSpace S :=
  circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (fun _ => 0) (sectorChartContinuousLinear S x)

/-- Decoding gives the literal inverse of the original root label. -/
theorem n04PositiveGeometry_leftRootInverseCircle_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
      (n04PositiveGeometry_leftRootInverseCircle hT hS hN x) m θ =
      Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m false) θ - θ := by
  have hd := congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
    (circlePositiveInversePerturbation_decode (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
      (by norm_num) (fun _ => 0) (sectorChartContinuousLinear S x)
      (leftRootChart_positive hS hN hx))
  have hi : circleAffineInverse (fun _ => 0) (sectorChartContinuousLinear S x) m θ =
      Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m false) θ :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f θ) (leftRootChart_lift hN x m)
  exact hd.trans (by rw [sub_zero, hi])

/-- Its tower is obtained from the actual positive inverse operator. -/
def n04PositiveGeometry_leftRootInverseCircle_directions
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (n04PositiveGeometry_leftRootInverseCircle hT hS hN) :=
  ((smoothTameOn_circlePositiveInversePerturbation (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1
    (by norm_num) (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 (fun _ => 0)).choose).compLinear
      (sectorChartContinuousLinear S) (sectorNeighborhood_isOpen S base ε ε)
      (fun _ hx => leftRootChart_positive hS hN hx)

/-- One low order works for all parameter orders of every genuine tower
of the actual left-root inverse displacement. -/
theorem n04PositiveGeometry_leftRootInverseCircle_fixedBase_oneHigh
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
          (n04PositiveGeometry_leftRootInverseCircle hT hS hN),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading B x ≤ R →
        ∀ v : Fin n → (StateDirections S × ℝ),
          (S.circle (3 / 4 : ℝ)).grading s (J.D n x v) ≤
            K * tameJetSize (pairGrading (sectorGrading S) realGrading) n s ell B x v :=
  n04PositiveGeometry_endpointBounds_inverseLinear_oneHigh
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (pairGrading (sectorGrading S) realGrading) (sectorChartContinuousLinear S)
    (sectorParameter_chart_grading_le S) (sectorNeighborhood_isOpen S base ε ε)
    (by norm_num : (0 : ℝ) < 1 / 2) (fun _ hx => leftRootChart_lower hN hx)

/-- The same low order controls all actual scalar angular jets, with
constants independent of the component, angle, and chosen scalar tower. -/
theorem n04PositiveGeometry_leftRootInverseDefect_fixedBase_oneHigh
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ b : ℕ, b ≤ s → ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
          (fun x => iteratedDeriv b (fun α =>
            Function.invFun (n01RootLabel S C (liftSectorParameter S C x) m false) α - α) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading B x ≤ R →
        ∀ v : Fin n → (StateDirections S × ℝ),
          |J.D n x v| ≤ K * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            tameJetSize (pairGrading (sectorGrading S) realGrading) n s ell B x v := by
  let JC := n04PositiveGeometry_leftRootInverseCircle_directions hT hS hN
  refine (n04PositiveGeometry_leftRootInverseCircle_fixedBase_oneHigh hT hS hN).elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro ell hell
  refine ⟨ell + 1, fun R hR s => ?_⟩
  refine (hell R hR (s + 1)).elim ?_
  intro K hK
  refine ⟨2 * circleSobolevConstant * K,
    mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hK.1, ?_⟩
  intro b hb m θ J x hx hxR v
  let J' : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => iteratedDeriv b ((S.circle (3 / 4 : ℝ)).decode
        (n04PositiveGeometry_leftRootInverseCircle hT hS hN y) m) θ) :=
    J.congrOn (fun y hy =>
      congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
        (funext (fun α =>
          (n04PositiveGeometry_leftRootInverseCircle_decode hT hS hN hy m α).symm)))
  exact n04PositiveGeometry_endpointBounds_angleEvaluation (hS.2.1 (3 / 4 : ℝ))
    (material_circle_sample_weights_pos hT hN.1.1).2
    (pairGrading (sectorGrading S) realGrading) JC hx v
    (hK.2 JC x hx hxR v) b hb m θ J'

end ContinuousFlexibility.Analysis
