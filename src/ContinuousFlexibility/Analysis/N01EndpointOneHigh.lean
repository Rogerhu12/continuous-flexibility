import ContinuousFlexibility.Analysis.N01EndpointJetLocalGrowth
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Actual endpoint jets satisfy one-high circle estimates

Algebraic multilinearity suffices for homogeneous normalization, so
continuity is proved from the estimates rather than assumed. The same
fixed low order and derivative loss work in all parameter orders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointOneHighStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_positive_circleNorm_oneHigh
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT (n + 1) z v) ≤
        K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          B (s + L) z v := by
  obtain ⟨B, L, hB, hbound⟩ :=
    hN.endpointFlowScalarJets_positive_circleNorm_local_growth hS hT
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  obtain ⟨K, hK, hk⟩ := hbound n R hR s hs
  refine ⟨K, hK, ?_⟩
  intro z hz hzb v
  let p := pairGrading (sectorGrading S) realGrading
  let A := hN.endpointFlowScalarJets hS hT (n + 1) z
  let M := liftCircleMultilinear (hS.2.1 (3 / 4 : ℝ)) A
    (hN.endpointFlowScalarJets_positive_circleMember hS hT n z hz)
  let coordinate := projectiveCoordinate
    (fun j => (S.circle (3 / 4 : ℝ)).level j) (S.circle (3 / 4 : ℝ)).bond s
  let F := coordinate.toLinearMap.compMultilinearMap M
  have hnorm (w : Fin (n + 1) → (StateDirections S × ℝ)) :
      ‖F w‖ = circleNorm T (3 / 4 : ℝ) s (A w) := by
    change ‖(M w).val s‖ = _
    rw [(hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2, liftCircleMultilinear_decode]
  have hunit : ∀ w : Fin (n + 1) → (StateDirections S × ℝ),
      (∀ i, p B (w i) < 1) →
      (normSeminorm ℝ ((S.circle (3 / 4 : ℝ)).level s)) (F w) ≤
        K * ((1 + p (s + L) z) + ∑ i, p (s + L) (w i)) := by
    intro w hw
    change ‖F w‖ ≤ _
    rw [hnorm]
    exact hk z hz hzb w (fun i => (hw i).le)
  have h := multilinearMap_bound_of_unitBall F
    (normSeminorm ℝ ((S.circle (3 / 4 : ℝ)).level s))
    (p B) (p (s + L)) hK hunit v
  change ‖F v‖ ≤ _ at h
  rw [hnorm] at h
  simpa only [multilinearTameSize, oneHighVariationWeight, p] using h

/-- Product estimates for genuine continuity on a bounded low-order
box. The sharper one-high theorem remains available for tame bounds. -/
theorem N01Properties.endpointFlowScalarJets_positive_norm_bounds_on_box
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ n s : ℕ,
      ∃ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT (n + 1) z v) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading j z) *
          ∏ i, pairGrading (sectorGrading S) realGrading j (v i) := by
  obtain ⟨B, L, hB, hbound⟩ :=
    hN.endpointFlowScalarJets_positive_circleNorm_oneHigh hS hT
  refine ⟨B, hB, fun R hR n s => ?_⟩
  let t : ℕ := max s B
  obtain ⟨K, hK, hk⟩ := hbound n R hR t (le_max_right _ _)
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  refine ⟨t + L, K * (((n + 1 : ℕ) : ℝ) + 1),
    mul_nonneg hK (by positivity), ?_⟩
  intro z hz hzb v
  have hW := oneHighVariationWeight_le_seminorm_product p (p (t + L)) B (t + L)
    (hp (by have hBt : B ≤ t := le_max_right _ _; omega)) le_rfl z v
  calc
    _ ≤ circleNorm T (3 / 4 : ℝ) t (hN.endpointFlowScalarJets hS hT (n + 1) z v) :=
      circleNorm_monotone_of_member
        (hN.endpointFlowScalarJets_positive_circleMember hS hT n z hz v) (le_max_left _ _)
    _ ≤ K * oneHighVariationWeight p B (t + L) z v := hk z hz hzb v
    _ ≤ K * ((((n + 1 : ℕ) : ℝ) + 1) * (1 + p (t + L) z) * ∏ i, p (t + L) (v i)) :=
      mul_le_mul_of_nonneg_left hW hK
    _ = _ := by dsimp only [p]; ring

end ContinuousFlexibility.Statements
