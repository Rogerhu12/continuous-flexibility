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

private theorem singleton_energy_constant_pos (s : ℕ) :
    0 < 1 + circleSingletonGradingConstant s * (2 * circleSobolevConstant) :=
  add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (circleSingletonGradingConstant_nonneg s)
      (mul_nonneg (by norm_num) circleSobolevConstant_nonneg))

private theorem oneHigh_split_energy_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (z : E)
    {n : ℕ} (vs : Fin n → E) (w : E)
    {K scale L₀ L₁ value : ℝ} {E₀ E₁ : ℝ≥0∞}
    (hK : 0 ≤ K) (hscale : 0 ≤ scale) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hvs : ∀ i, p base (vs i) ≤ 1)
    (hvalue : value ≤ K * scale *
      oneHighVariationWeight p base high z (Fin.snoc vs w))
    (hlow : scale * p base w ≤ L₀ * Real.sqrt E₀.toReal)
    (hhigh : scale * p high w ≤ L₁ * Real.sqrt E₁.toReal) :
    value ≤ K * (L₀ + L₁) *
      ((1 + p high z + ∑ i : Fin n, p high (vs i)) * Real.sqrt E₀.toReal +
        Real.sqrt E₁.toReal) := by
  let A : ℝ := 1 + p high z + ∑ i : Fin n, p high (vs i)
  have hA : 0 ≤ A := add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
    (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  have hlow' : scale * p base w ≤ (L₀ + L₁) * Real.sqrt E₀.toReal :=
    hlow.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL₁) (Real.sqrt_nonneg _))
  have hhigh' : scale * p high w ≤ (L₀ + L₁) * Real.sqrt E₁.toReal :=
    hhigh.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL₀) (Real.sqrt_nonneg _))
  have hW := oneHighVariationWeight_snoc_le_of_low_le_one p base high z vs w hvs
  calc
    value ≤ K * scale * oneHighVariationWeight p base high z (Fin.snoc vs w) := hvalue
    _ ≤ K * scale * (A * p base w + p high w) :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg hK hscale)
    _ = K * (A * (scale * p base w) + scale * p high w) := by ring
    _ ≤ K * (A * ((L₀ + L₁) * Real.sqrt E₀.toReal) +
        (L₀ + L₁) * Real.sqrt E₁.toReal) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hlow' hA) hhigh') hK
    _ = _ := by dsimp only [A]; ring

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
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + hN.ordinaryFlowLoss (n + 1)) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + hN.ordinaryFlowLoss (n + 1)) (vs i)) *
            Real.sqrt (stateLocalizationEnergy D T C base (c + 1) v m).toReal +
          Real.sqrt (stateLocalizationEnergy D T C (b + hN.ordinaryFlowLoss (n + 1)) (c + 1) v m).toReal) := by
  let boundData := N01Properties.endpointFlowScalarJets_weighted_bound_uniform_radius
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT (n + 1) b
  let K : ℝ := boundData.choose
  have hK : 0 < K := boundData.choose_spec.1
  let L₀ : ℝ := 1 + circleSingletonGradingConstant base * (2 * circleSobolevConstant)
  let L₁ : ℝ := 1 + circleSingletonGradingConstant (b + hN.ordinaryFlowLoss (n + 1)) * (2 * circleSobolevConstant)
  have hL₀ : 0 < L₀ := singleton_energy_constant_pos base
  have hL₁ : 0 < L₁ := singleton_energy_constant_pos (b + hN.ordinaryFlowLoss (n + 1))
  refine ⟨K * (L₀ + L₁), mul_pos hK (add_pos hL₀ hL₁), ?_⟩
  intro rsel hrsel z hz vs hvs v hvq
  let localData := N01Properties.exists_localized_state_energy_directions
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT v hvq
  let w : ℕ → (StateDirections S × ℝ) := localData.choose
  intro m θ
  have hD : IsAccumulatingProfile D := hN.1.1
  have hgeom : AccumulatingProfileBounds D hD.choose := hD.choose_spec
  have hM : 0 ≤ T.M (T.sample m) := zero_le_one.trans
    (hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 m)).2.2.2
  have heq :
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ =
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs (w m)) m) θ :=
    (hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1)
      z hz (Fin.snoc vs v) m b θ).trans
        ((localData.choose_spec.2.1 m n b θ (rsel m) (hrsel m)
          (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
            (hrsel m) b θ) z hz vs).trans
          (hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1)
            z hz (Fin.snoc vs (w m)) m b θ).symm)
  have hpoint :
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
          |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1)
            z (Fin.snoc vs v) m) θ| ≤
        K * T.M (T.sample m) ^ (c + 1) *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (b + hN.ordinaryFlowLoss (n + 1)) z (Fin.snoc vs (w m)) :=
    (congrArg (fun a : ℝ =>
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) * |a|) heq).trans_le
        (boundData.choose_spec.2 rsel hrsel m b c θ le_rfl z hz (Fin.snoc vs (w m)))
  exact oneHigh_split_energy_bound (pairGrading (sectorGrading S) realGrading)
    base (b + hN.ordinaryFlowLoss (n + 1)) z vs (w m) hK.le (pow_nonneg hM (c + 1)) hL₀.le hL₁.le hvs
    hpoint (localData.choose_spec.2.2 m base (c + 1))
      (localData.choose_spec.2.2 m (b + hN.ordinaryFlowLoss (n + 1)) (c + 1))

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
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + hN.ordinaryFlowLoss (n + 1)) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + hN.ordinaryFlowLoss (n + 1)) (vs i)) *
            Real.sqrt (stateLocalizationEnergy D T C base (c + 1) v m).toReal +
          Real.sqrt (stateLocalizationEnergy D T C (b + hN.ordinaryFlowLoss (n + 1)) (c + 1) v m).toReal) := by
  let data := N01Properties.endpointFlowScalarJets_state_split_energy_bound_uniform_radius
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT n b c
  exact ⟨data.choose, data.choose_spec.1, data.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
