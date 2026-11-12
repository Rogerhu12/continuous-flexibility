import ContinuousFlexibility.Analysis.N01EndpointJetLocalGrowth
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Actual endpoint jets satisfy one-high circle estimates

Algebraic multilinearity suffices for homogeneous normalization, so
continuity is proved from the estimates rather than assumed. The same
low order and derivative loss are fixed at each parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointOneHighStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem real_mul_four_reassociate (K N a b : ℝ) :
    K * (N * a * b) = (K * N) * a * b := by
  simp only [mul_assoc]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∀ n : ℕ, ∃ B L : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          B (s + L) z v := by
  intro n
  let data := hN.endpointFlowScalarJets_positive_circleNorm_local_growth_uniform_radius hS hT n
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 R hR s hs
  let K : ℝ := orderData.choose
  have hK : 0 ≤ K := orderData.choose_spec.1
  refine ⟨K, hK, ?_⟩
  intro rsel hrsel z hz hzb v
  let p := pairGrading (sectorGrading S) realGrading
  let A := hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
  let M := liftCircleMultilinear (hS.2.1 (3 / 4 : ℝ)) A
    (hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz)
  let coordinate := projectiveCoordinate
    (fun j => (S.circle (3 / 4 : ℝ)).level j) (S.circle (3 / 4 : ℝ)).bond s
  let F := coordinate.toLinearMap.compMultilinearMap M
  have hnorm (w : Fin (n + 1) → (StateDirections S × ℝ)) :
      ‖F w‖ = circleNorm T (3 / 4 : ℝ) s (A w) := by
    have hlevel : ‖(M w).val s‖ =
        circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode (M w)) :=
      (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2 (M w) s
    have hdecode : (S.circle (3 / 4 : ℝ)).decode (M w) = A w :=
      liftCircleMultilinear_decode (hS.2.1 (3 / 4 : ℝ)) A
        (hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz) w
    exact (show ‖F w‖ = ‖(M w).val s‖ from rfl).trans
      (hlevel.trans (congrArg (circleNorm T (3 / 4 : ℝ) s) hdecode))
  have hunit : ∀ w : Fin (n + 1) → (StateDirections S × ℝ),
      (∀ i, p B (w i) < 1) →
      (normSeminorm ℝ ((S.circle (3 / 4 : ℝ)).level s)) (F w) ≤
        K * ((1 + p (s + L) z) + ∑ i, p (s + L) (w i)) := by
    intro w hw
    exact (hnorm w).trans_le
      (orderData.choose_spec.2 rsel hrsel z hz hzb w (fun i => (hw i).le))
  have h := multilinearMap_bound_of_unitBall F
    (normSeminorm ℝ ((S.circle (3 / 4 : ℝ)).level s))
    (p B) (p (s + L)) hK hunit v
  exact (hnorm v).symm.trans_le h

theorem N01Properties.endpointFlowScalarJets_positive_circleNorm_oneHigh
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∀ n : ℕ, ∃ B L : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          B (s + L) z v := by
  intro n
  let data := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius hS hT n
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 R hR s hs
  exact ⟨orderData.choose, orderData.choose_spec.1, orderData.choose_spec.2 rsel hrsel⟩

/-- Product estimates for genuine continuity on a bounded low-order
box. The sharper one-high theorem remains available for tame bounds. -/
theorem N01Properties.endpointFlowScalarJets_positive_norm_bounds_on_box
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∀ n : ℕ, ∃ B : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading j z) *
          ∏ i, pairGrading (sectorGrading S) realGrading j (v i) := by
  intro n
  let data := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh hS hT rsel hrsel n
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, hB, fun R hR s => ?_⟩
  let t : ℕ := max s B
  let orderData := data.choose_spec.choose_spec.2 R hR t (le_max_right _ _)
  let K : ℝ := orderData.choose
  have hK : 0 ≤ K := orderData.choose_spec.1
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  refine ⟨t + L, K * (((n + 1 : ℕ) : ℝ) + 1),
    mul_nonneg hK (by positivity), ?_⟩
  intro z hz hzb v
  have hW := oneHighVariationWeight_le_seminorm_product p (p (t + L)) B (t + L)
    (hp (by have hBt : B ≤ t := le_max_right _ _; omega)) le_rfl z v
  calc
    _ ≤ circleNorm T (3 / 4 : ℝ) t (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) :=
      circleNorm_monotone_of_member
        (hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz v) (le_max_left _ _)
    _ ≤ K * oneHighVariationWeight p B (t + L) z v := orderData.choose_spec.2 z hz hzb v
    _ ≤ K * ((((n + 1 : ℕ) : ℝ) + 1) * (1 + p (t + L) z) * ∏ i, p (t + L) (v i)) :=
      mul_le_mul_of_nonneg_left hW hK
    _ = _ := real_mul_four_reassociate K (((n + 1 : ℕ) : ℝ) + 1)
      (1 + p (t + L) z) (∏ i, p (t + L) (v i))

end ContinuousFlexibility.Statements
