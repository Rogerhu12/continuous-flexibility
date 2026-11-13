import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseCompositionBounds
import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseInterpolation
import ContinuousFlexibility.Analysis.N04EndpointCircleFixedBaseBounds
import ContinuousFlexibility.Analysis.N01ReturnCircleUniformBounds

/-!
# A common low order for the actual inverse-circle families

The generic operator and composition estimates retain their input base
when applied to the actual closed-radius characteristic selectors. The
inverse displacement is the negative diagonal of the same operator.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

local instance n04NegativeGeometryInverseBoundsCircleSMul (H : CircleModelData) :
    SMul ℝ (H.Space × H.Space) := Prod.instSMul

local instance n04NegativeGeometryInverseBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The genuine inverse displacement of every closed-radius selector has
one common low order. Its bound is uniform in the selector and in the
choice of genuine tower of that same actual inverse. -/
theorem N01Properties.n04NegativeGeometry_selectorInverseCircle_fixedBase_oneHigh
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ) :
    ∃ B : ℕ, base ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.selectorInverseCircle hS hT rsel hrsel),
      ∀ x ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        (S.circle (3 / 4 : ℝ)).grading s (J.D n x v) ≤
          K * tameJetSize (pairGrading (sectorGrading S) realGrading) n s L B x v := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  let H := S.circle (3 / 4 : ℝ)
  let U := sectorNeighborhood S base ε ε
  let I := {rsel : ℕ → ℝ // ∀ m, rsel m ∈ Icc (C.left m) (C.right m)}
  let f : I → (StateDirections S × ℝ) → H.Space :=
    fun i => hN.endpointFlowCircle hS hT i.val i.property
  let J : ∀ i, SmoothDirections U (f i) :=
    fun i => (hN.exists_endpointFlowCircle_smoothDirections hS hT i.val i.property).choose
  let P : ∀ i, SmoothDirections U (fun x => (f i x, f i x)) :=
    fun i => smoothDirectionsProd (J i) (J i)
  let source := hN.endpointFlowCircle_fixedBase_oneHigh hS hT
  let BJ : ℕ := source.choose
  have hP : ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, x ∈ U → p BJ x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        pairGrading H.grading H.grading s ((P i).D n x v) ≤
          K * tameJetSize p n s L BJ x v := by
    intro n
    let lossData := source.choose_spec.2 n
    let L : ℕ := lossData.choose
    refine ⟨L, fun R hR s => ?_⟩
    let bound := lossData.choose_spec R hR s
    let K : ℝ := bound.choose
    have hK : 0 ≤ K := bound.choose_spec.1
    refine ⟨K + K, add_nonneg hK hK, fun i x hx hlow v => ?_⟩
    have h := bound.choose_spec.2 i.val i.property (J i) x hx hlow v
    have hdiag : pairGrading H.grading H.grading s ((P i).D n x v) =
        H.grading s ((J i).D n x v) + H.grading s ((J i).D n x v) :=
      n04NegativeGeometry_diagonalTower_grading (J i) n s x v
    rw [hdiag]
    simpa only [add_mul] using add_le_add h h
  have hp : Monotone p := sectorPairGrading_monotone S
  have hIp : HasInterpolation (pairGrading realGrading p) :=
    n04NegativeGeometry_inverseBounds_parameterInterpolation hS
  have hlower (i : I) (x : StateDirections S × ℝ) (hx : x ∈ U) (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ 1 + deriv (H.decode (f i x) m) θ := by
    rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ))
      (fun j => -opticalTravel D.w (C.left j) (i.val j)),
      hN.endpointFlowCircle_affineLift hS hT i.val i.property x hx]
    exact hflow x hx m (i.val m) (i.property m) θ
  let inverse := n04NegativeGeometry_circleInverse_fixedBase_oneHigh
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2 p hp hIp P BJ hP
    (fun i m => -opticalTravel D.w (C.left m) (i.val m)) (1 / 2) (by norm_num) hlower
  let B : ℕ := inverse.choose
  refine ⟨B, source.choose_spec.1.trans inverse.choose_spec.1, fun n => ?_⟩
  let lossData := inverse.choose_spec.2 n
  let L : ℕ := lossData.choose
  refine ⟨L, fun R hR s => ?_⟩
  let bound := lossData.choose_spec R hR s
  refine ⟨bound.choose, bound.choose_spec.1, fun rsel hrsel Jinv x hx hlow v => ?_⟩
  let i : I := ⟨rsel, hrsel⟩
  let Jpositive : SmoothDirections U (fun x =>
      circlePositiveInverseComposeLinear (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
        (fun m => -opticalTravel D.w (C.left m) (rsel m)) (f i x) (f i x)) :=
    (solveSmoothDirectionsPostcomp Jinv (-ContinuousLinearMap.id ℝ H.Space)).congrOn
      (fun x _ => by
        change -(-circlePositiveInverseComposeLinear _ _ _ _ _ _ _) = _
        exact neg_neg _)
  have h := bound.choose_spec.2 i Jpositive x hx hlow v
  change H.grading s (-Jinv.D n x v) ≤ _ at h
  simpa only [map_neg_eq_map] using h

end ContinuousFlexibility.Statements
