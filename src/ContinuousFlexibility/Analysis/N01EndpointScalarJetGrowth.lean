import ContinuousFlexibility.Analysis.N01EndpointScalarSplitNorm
import ContinuousFlexibility.Analysis.CircleWeightedJetNormSum
import ContinuousFlexibility.Analysis.LocalizedJetInterpolation
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Fixed-loss local growth of all pure scalar endpoint jets

The actual physical height factor is estimated before interpolation.
The resulting circle norm has one high base-point seminorm, with a loss
chosen independently of both the output order and the local radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointScalarJetGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem finite_weighted_sum_mul_reassociate
    {ι : Type*} [Fintype ι] (K : ι → ℝ) (I A : ℝ) :
    (∑ j : ι, K j * (I * A)) = (∑ j : ι, K j) * I * A := by
  classical
  rw [← Finset.sum_mul]
  exact (mul_assoc _ _ _).symm

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlow_pure_scalar_circleNorm_local_growth_all_uniform_radius
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z) := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  let interpolationData := hasInterpolation_quadratic_local_growth p hp hI base loss 6
  let B : ℕ := interpolationData.choose
  let L : ℕ := interpolationData.choose_spec.choose
  have hB : base ≤ B := interpolationData.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := interpolationData.choose_spec.choose_spec.2 R hR s hs
  let I : ℝ := orderData.choose
  have hI0 : 0 ≤ I := orderData.choose_spec.1
  let rawData (j : CircleJetIndex s) :=
    hN.endpointFlow_pure_scalar_weightedJetNorm_budget_bound_uniform_radius hS hT n (j.val 0).val (j.val 1).val
  let K : CircleJetIndex s → ℝ := fun j => (rawData j).choose
  have hK (j : CircleJetIndex s) : 0 ≤ K j := (rawData j).choose_spec.1
  refine ⟨(∑ j : CircleJetIndex s, K j) * I,
    mul_nonneg (Finset.sum_nonneg (fun j _ => hK j)) hI0, ?_⟩
  intro rsel hrsel z hz hzb
  calc
    _ ≤ ∑ j : CircleJetIndex s, circleWeightedJetNorm T (3 / 4 : ℝ)
        (j.val 0).val (j.val 1).val (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) :=
      circleNorm_le_sum_weightedJetNorm
        (hN.endpointFlow_pure_scalar_circleMember hS hT rsel hrsel n z hz) s
    _ ≤ ∑ j : CircleJetIndex s, K j * (I * (1 + p (s + L) z)) := by
      apply Finset.sum_le_sum
      intro j _
      exact ((rawData j).choose_spec.2 rsel hrsel z hz).trans (mul_le_mul_of_nonneg_left
        (orderData.choose_spec.2 _ _ j.property z hzb) (hK j))
    _ = _ := finite_weighted_sum_mul_reassociate K I (1 + p (s + L) z)

theorem N01Properties.endpointFlow_pure_scalar_circleNorm_local_growth_all
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z) := by
  let data := hN.endpointFlow_pure_scalar_circleNorm_local_growth_all_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  exact ⟨orderData.choose, orderData.choose_spec.1, orderData.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
