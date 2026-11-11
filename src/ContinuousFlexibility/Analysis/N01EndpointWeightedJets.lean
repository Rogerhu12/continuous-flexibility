import ContinuousFlexibility.Analysis.N01EndpointCircleJets
import ContinuousFlexibility.Analysis.N01FlowSamplePrefactor

/-!
# The chosen endpoint jets with their exact circle weights

Every angular N01 estimate retains its original one-high expression.
The complete height and material prefactor costs one material order,
uniformly in both the angular order and the number of parameter slots.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointWeightedJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointWeightedJetsRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_weighted_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (k s : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ m b c θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin k → (StateDirections S × ℝ),
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel k z v m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  obtain ⟨B, hB, hbound⟩ := hN.sectorFlow_closed_angularTower_bound hS hT k s
  obtain ⟨K, hK, hpref⟩ := hN.flow_sample_prefactor_le_M hT hB.le
  refine ⟨B * K, mul_pos hB hK, fun rsel hrsel m b c θ hb z hz v => ?_⟩
  have hs := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ hs).2.2.2
  have hH : 0 ≤ T.H (T.sample m) := (hT.2.1 _ hs).2.1.le
  let W : ℝ := oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
    base (s + loss) z v
  have hW : 0 ≤ W := by
    dsimp only [W, oneHighVariationWeight]
    exact add_nonneg
      (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
        (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (apply_nonneg _ _)
        (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))))
  have hj := hbound m (rsel m) (hrsel m)
    b θ hb z hz v
  rw [hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel k z hz]
  calc
    _ ≤ (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B * W) :=
      mul_le_mul_of_nonneg_left hj
        (mul_nonneg (pow_nonneg hM c) (Real.rpow_nonneg hH _))
    _ = (B * T.M (T.sample m) ^ c) *
        (T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
          T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B) * W := by ring
    _ ≤ (B * T.M (T.sample m) ^ c) * (K * T.M (T.sample m)) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpref m) (mul_nonneg hB.le (pow_nonneg hM c))) hW
    _ = _ := by rw [pow_succ]; dsimp only [W]; ring

theorem N01Properties.endpointFlowScalarJets_weighted_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (k s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m b c θ, b ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin k → (StateDirections S × ℝ),
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel k z v m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  obtain ⟨K, hK, hbound⟩ := hN.endpointFlowScalarJets_weighted_bound_uniform_radius hS hT k s
  exact ⟨K, hK, hbound rsel hrsel⟩

end ContinuousFlexibility.Statements
