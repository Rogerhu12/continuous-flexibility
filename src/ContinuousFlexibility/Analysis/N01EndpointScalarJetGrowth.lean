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

theorem N01Properties.endpointFlow_pure_scalar_circleNorm_local_growth_all
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT (n + 1) z
          (fun _ => scalarParameterDirection S)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z) := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  obtain ⟨B, L, hB, hinterp⟩ := hasInterpolation_quadratic_local_growth p hp hI base loss 6
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  obtain ⟨I, hI0, hi⟩ := hinterp R hR s hs
  have hraw (j : CircleJetIndex s) :=
    hN.endpointFlow_pure_scalar_weightedJetNorm_budget_bound hS hT n (j.val 0).val (j.val 1).val
  choose K hK hk using hraw
  refine ⟨(∑ j : CircleJetIndex s, K j) * I,
    mul_nonneg (Finset.sum_nonneg (fun j _ => hK j)) hI0, ?_⟩
  intro z hz hzb
  calc
    _ ≤ ∑ j : CircleJetIndex s, circleWeightedJetNorm T (3 / 4 : ℝ)
        (j.val 0).val (j.val 1).val (hN.endpointFlowScalarJets hS hT (n + 1) z
          (fun _ => scalarParameterDirection S)) :=
      circleNorm_le_sum_weightedJetNorm
        (hN.endpointFlow_pure_scalar_circleMember hS hT n z hz) s
    _ ≤ ∑ j : CircleJetIndex s, K j * (I * (1 + p (s + L) z)) := by
      apply Finset.sum_le_sum
      intro j _
      exact (hk j z hz).trans (mul_le_mul_of_nonneg_left
        (hi _ _ j.property z hzb) (hK j))
    _ = _ := by
      rw [← Finset.sum_mul]
      dsimp only [p]
      ring

end ContinuousFlexibility.Statements
