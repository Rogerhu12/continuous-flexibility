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

private theorem weighted_abs_bound_of_prefactor
    {M u v e B K W a : ℝ} (c : ℕ)
    (hM : 0 ≤ M) (hu : 0 ≤ u) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hjet : |a| ≤ B * v * e * W) (hpref : u * v * e ≤ K * M) :
    (M ^ c * u) * |a| ≤ (B * K) * M ^ (c + 1) * W := by
  calc
    _ ≤ (M ^ c * u) * (B * v * e * W) :=
      mul_le_mul_of_nonneg_left hjet (mul_nonneg (pow_nonneg hM c) hu)
    _ = (B * M ^ c) * (u * v * e) * W := by ring
    _ ≤ (B * M ^ c) * (K * M) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpref (mul_nonneg hB (pow_nonneg hM c))) hW
    _ = _ := by rw [pow_succ]; ring

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
  let hdata := hN.sectorFlow_closed_angularTower_bound hS hT k s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  let hprefData := hN.flow_sample_prefactor_le_M hT hB.le
  let K : ℝ := hprefData.choose
  have hK : 0 < K := hprefData.choose_spec.1
  refine ⟨B * K, mul_pos hB hK, fun rsel hrsel m b c θ hb z hz v => ?_⟩
  have hs := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ hs).2.2.2
  have hH : 0 ≤ T.H (T.sample m) := (hT.2.1 _ hs).2.1.le
  have hW : 0 ≤ oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
      base (s + loss) z v :=
    multilinearTameSize_nonneg _ _ _
      (add_nonneg zero_le_one (apply_nonneg _ _)) v
  have hj : |iteratedDeriv b
        (hN.endpointFlowScalarJets hS hT rsel hrsel k z v m) θ| ≤
      B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          base (s + loss) z v :=
    (congrArg abs (hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel
      k z hz v m b θ)).trans_le
        (hdata.choose_spec.2 m (rsel m) (hrsel m) b θ hb z hz v)
  exact weighted_abs_bound_of_prefactor c hM (Real.rpow_nonneg hH _) hB.le hW hj
    (hprefData.choose_spec.2 m)

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
  let hdata := hN.endpointFlowScalarJets_weighted_bound_uniform_radius hS hT k s
  exact ⟨hdata.choose, hdata.choose_spec.1, hdata.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
