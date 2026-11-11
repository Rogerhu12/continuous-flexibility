import ContinuousFlexibility.Analysis.N01EndpointStateCircleMember
import ContinuousFlexibility.Analysis.OneHighLocalizedSlot

/-!
# Separate angular and material orders in the actual endpoint jets

The two summable envelopes retain different local derivative orders.
For an angular order b and a material degree c their total physical
orders are base+c+6 and b+loss+c+6. This separation is the input for the
fixed-loss interpolation argument.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointSplitEnergyStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointSplitEnergyRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_state_split_energy_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n b c : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading base (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ, v.2 = 0 → ∀ m θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ| ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + loss) (vs i)) *
            Real.sqrt (stateLocalizationEnergy D T C base (c + 1) v m).toReal +
          Real.sqrt (stateLocalizationEnergy D T C (b + loss) (c + 1) v m).toReal) := by
  obtain ⟨K, hK, hpoint⟩ := hN.endpointFlowScalarJets_weighted_bound_uniform_radius hS hT (n + 1) b
  let L₀ : ℝ := 1 + circleSingletonGradingConstant base * (2 * circleSobolevConstant)
  let L₁ : ℝ := 1 + circleSingletonGradingConstant (b + loss) * (2 * circleSobolevConstant)
  have hL₀ : 0 < L₀ := by
    have h := mul_nonneg (circleSingletonGradingConstant_nonneg base)
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) circleSobolevConstant_nonneg)
    dsimp only [L₀]
    linarith only [h]
  have hL₁ : 0 < L₁ := by
    have h := mul_nonneg (circleSingletonGradingConstant_nonneg (b + loss))
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) circleSobolevConstant_nonneg)
    dsimp only [L₁]
    linarith only [h]
  let L : ℝ := L₀ + L₁
  have hL : 0 < L := add_pos hL₀ hL₁
  refine ⟨K * L, mul_pos hK hL, ?_⟩
  intro rsel hrsel z hz vs hvs v hvq
  obtain ⟨w, _, hlocal, henergy⟩ :=
    hN.exists_localized_state_energy_directions hS hT v hvq
  intro m θ
  let p := pairGrading (sectorGrading S) realGrading
  let A : ℝ := 1 + p (b + loss) z + ∑ i : Fin n, p (b + loss) (vs i)
  have hA : 0 ≤ A := add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
    (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans
    (hT.2.1 _ (materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m)).2.2.2
  have heq :
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ =
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs (w m)) m) θ := by
    rw [hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1) z hz,
      hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1) z hz]
    exact hlocal m n b θ (rsel m) (hrsel m)
      (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
        (hrsel m) b θ) z hz vs
  have hlow : T.M (T.sample m) ^ (c + 1) * p base (w m) ≤
      L * Real.sqrt (stateLocalizationEnergy D T C base (c + 1) v m).toReal :=
    (henergy m base (c + 1)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL₁.le) (Real.sqrt_nonneg _))
  have hhigh : T.M (T.sample m) ^ (c + 1) * p (b + loss) (w m) ≤
      L * Real.sqrt (stateLocalizationEnergy D T C (b + loss) (c + 1) v m).toReal :=
    (henergy m (b + loss) (c + 1)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL₀.le) (Real.sqrt_nonneg _))
  have hW := oneHighVariationWeight_snoc_le_of_low_le_one p base (b + loss) z vs (w m) hvs
  rw [heq]
  calc
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        oneHighVariationWeight p base (b + loss) z (Fin.snoc vs (w m)) :=
      hpoint rsel hrsel m b c θ le_rfl z hz (Fin.snoc vs (w m))
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        (A * p base (w m) + p (b + loss) (w m)) :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg hK.le (pow_nonneg hM _))
    _ = K * (A * (T.M (T.sample m) ^ (c + 1) * p base (w m)) +
        T.M (T.sample m) ^ (c + 1) * p (b + loss) (w m)) := by ring
    _ ≤ K * (A * (L *
        Real.sqrt (stateLocalizationEnergy D T C base (c + 1) v m).toReal) +
      L * Real.sqrt (stateLocalizationEnergy D T C (b + loss) (c + 1) v m).toReal) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hlow hA) hhigh) hK.le
    _ = _ := by dsimp only [A, p]; ring

theorem N01Properties.endpointFlowScalarJets_state_split_energy_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n b c : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading base (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ, v.2 = 0 → ∀ m θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ| ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + loss) (vs i)) *
            Real.sqrt (stateLocalizationEnergy D T C base (c + 1) v m).toReal +
          Real.sqrt (stateLocalizationEnergy D T C (b + loss) (c + 1) v m).toReal) := by
  obtain ⟨K, hK, hbound⟩ := hN.endpointFlowScalarJets_state_split_energy_bound_uniform_radius hS hT n b c
  exact ⟨K, hK, hbound rsel hrsel⟩

end ContinuousFlexibility.Statements
