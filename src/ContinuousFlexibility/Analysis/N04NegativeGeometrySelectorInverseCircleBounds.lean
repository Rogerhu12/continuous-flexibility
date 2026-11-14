module

public import ContinuousFlexibility.Analysis.N04NegativeChartReturnCircleBounds

/-! One common low base for all actual ordinary-flow inverse selectors. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

/- Use the same cached state instances as the statement layer. -/
attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

private theorem selectorInverse_allTowers
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (q : ℕ → Seminorm ℝ F)
    {U : Set E} {A : I → Prop} {f : (i : I) → A i → E → F}
    (base : ℕ)
    (hf : N04FixedBaseSmoothFamilyOn p q U (fun i : {i // A i} => f i.val i.property)) :
    ∃ B : ℕ, base ≤ B ∧ ∀ n : ℕ, ∃ L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ i hi (J : SmoothDirections U (f i hi)),
      ∀ x ∈ U, p B x ≤ R → ∀ v : Fin n → E,
        q s (J.D n x v) ≤ K * tameJetSize p n s L B x v := by
  obtain ⟨J₀, B₀, hb⟩ := hf
  refine ⟨max B₀ base, le_max_right _ _, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨K, hK, hbound⟩ := hL R hR s
  refine ⟨K, hK, fun i hi J x hx hlow v => ?_⟩
  rw [J.unique (J₀ ⟨i, hi⟩) n x hx]
  exact (hbound ⟨i, hi⟩ x hx ((hp (le_max_left _ _) x).trans hlow) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp le_rfl (le_max_left _ _) n s x v) hK)

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
  letI : ContinuousNeg (S.circle (3 / 4 : ℝ)).Space :=
    (withSeminorms_graded (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond).isTopologicalAddGroup.toContinuousNeg
  let I : Type := {rsel : ℕ → ℝ // ∀ m, rsel m ∈ Icc (C.left m) (C.right m)}
  have hf := hN.n04FixedBase_endpointFlowCircle hS hT
    (fun i : I => i.val) (fun i => i.property)
  have hlower (i : I) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε) (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ 1 + deriv ((S.circle (3 / 4 : ℝ)).decode
        (hN.endpointFlowCircle hS hT i.val i.property x) m) θ := by
    rw [← circleAffineLift_deriv (hS.2.1 (3 / 4 : ℝ))
      (fun j => -opticalTravel D.w (C.left j) (i.val j)),
      hN.endpointFlowCircle_affineLift hS hT i.val i.property x hx]
    exact hflow x hx m (i.val m) (i.property m) θ
  have hi := n04FixedBaseSmoothFamilyOn_circleInverse_maps
    (hS.2.1 (3 / 4 : ℝ)) hT hN.1.1 (by norm_num)
    (hS.2.2.2.2.1 (3 / 4 : ℝ)).2.2
    (fun i : I => fun m => -opticalTravel D.w (C.left m) (i.val m))
    (1 / 2) (by norm_num) (sectorPairGrading_monotone S)
    (n04FixedBase_sectorParameter_hasInterpolation hS)
    (sectorNeighborhood_isOpen S base ε ε) hlower hf hf
  exact selectorInverse_allTowers (pairGrading (sectorGrading S) realGrading)
    (sectorPairGrading_monotone S) (S.circle (3 / 4 : ℝ)).grading
    (f := fun r hr => hN.selectorInverseCircle hS hT r hr) base hi.neg


end ContinuousFlexibility.Statements
