import ContinuousFlexibility.Analysis.N01EndpointSplitEnergy
import ContinuousFlexibility.Analysis.CircleTwoEnergyEnvelope

/-!
# Actual endpoint estimates with the angular-material budget intact

This is a single weighted jet norm before the finite circle jet sum.
The low localized slot costs base+c+6, whereas the high localized slot
costs b+loss+d+c+6, with d fixed for each parameter order. The numerical
constant is independent of the state and all directions.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointSplitNormStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointSplitNormRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

def circleWeightedJetNorm (T : MaterialData) (γ : ℝ) (b c : ℕ)
    (v : ℕ → ℝ → ℝ) : ℝ :=
  Real.sqrt (∑' m : ℕ, ENNReal.ofReal
    ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure ^ 2).toReal

theorem weightedJetNorm_le_scaled_two_envelopes
    {T : MaterialData} {γ : ℝ} {v : ℕ → ℝ → ℝ}
    {E F : ℕ → ℝ≥0∞} {K K₀ K₁ A u₀ u₁ : ℝ}
    (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hA : 0 ≤ A) (hu₀ : 0 ≤ u₀) (hu₁ : 0 ≤ u₁)
    (hE : (∑' m, E m) ≤ ENNReal.ofReal (K₀ * u₀ ^ 2))
    (hF : (∑' m, F m) ≤ ENNReal.ofReal (K₁ * u₁ ^ 2))
    (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (b c : ℕ)
    (hpoint : ∀ m θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      K * (A * Real.sqrt (E m).toReal + Real.sqrt (F m).toReal)) :
    circleWeightedJetNorm T γ b c v ≤
      Real.sqrt (2 * Real.pi) * K * (Real.sqrt K₀ + Real.sqrt K₁) *
        (A * u₀ + u₁) := by
  have hEsq : (∑' m, E m) ≤ ENNReal.ofReal ((Real.sqrt K₀ * u₀) ^ 2) :=
    hE.trans_eq (congrArg ENNReal.ofReal (by rw [mul_pow, Real.sq_sqrt hK₀]))
  have hFsq : (∑' m, F m) ≤ ENNReal.ofReal ((Real.sqrt K₁ * u₁) ^ 2) :=
    hF.trans_eq (congrArg ENNReal.ofReal (by rw [mul_pow, Real.sq_sqrt hK₁]))
  have hpoint' (m : ℕ) (θ : ℝ) :
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      (K * A) * Real.sqrt (E m).toReal + K * Real.sqrt (F m).toReal :=
    (hpoint m θ).trans_eq (by ring)
  have hn := circleWeightedJetNorm_le_two_envelopes
    (mul_nonneg hK hA) hK
    (mul_nonneg (Real.sqrt_nonneg _) hu₀) (mul_nonneg (Real.sqrt_nonneg _) hu₁)
    hEsq hFsq hv hM hH b c hpoint'
  have h₀ : Real.sqrt K₀ ≤ Real.sqrt K₀ + Real.sqrt K₁ :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have h₁ : Real.sqrt K₁ ≤ Real.sqrt K₀ + Real.sqrt K₁ :=
    le_add_of_nonneg_left (Real.sqrt_nonneg _)
  calc
    circleWeightedJetNorm T γ b c v ≤
        Real.sqrt (2 * Real.pi) *
          (K * A * (Real.sqrt K₀ * u₀) + K * (Real.sqrt K₁ * u₁)) := hn
    _ = Real.sqrt (2 * Real.pi) * K *
        (A * (Real.sqrt K₀ * u₀) + Real.sqrt K₁ * u₁) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * K *
        (A * ((Real.sqrt K₀ + Real.sqrt K₁) * u₀) +
          (Real.sqrt K₀ + Real.sqrt K₁) * u₁) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₀ hu₀) hA)
          (mul_le_mul_of_nonneg_right h₁ hu₁))
        (mul_nonneg (Real.sqrt_nonneg _) hK)
    _ = _ := by ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_state_weightedJetNorm_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n : ℕ) :
    ∃ d : ℕ, ∀ b c : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading base (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ, v.2 = 0 →
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss + d) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + loss + d) (vs i)) *
            pairGrading (sectorGrading S) realGrading (base + c + 6) v +
          pairGrading (sectorGrading S) realGrading (b + loss + d + c + 6) v) := by
  let lossData := hN.endpointFlowScalarJets_state_split_energy_bound_uniform_radius hS hT n
  let d : ℕ := lossData.choose
  let horders := lossData.choose_spec
  refine ⟨d, ?_⟩
  intro b c
  let pointData := horders b c
  let K : ℝ := pointData.choose
  have hK : 0 < K := pointData.choose_spec.1
  let lowData := hN.stateLocalizationEnergy_tsum_le_grading_sq hS hT base (c + 1)
  let K₀ : ℝ := lowData.choose
  have hK₀ : 0 ≤ K₀ := lowData.choose_spec.1
  let highData := hN.stateLocalizationEnergy_tsum_le_grading_sq hS hT (b + loss + d) (c + 1)
  let K₁ : ℝ := highData.choose
  have hK₁ : 0 ≤ K₁ := highData.choose_spec.1
  let L : ℝ := Real.sqrt K₀ + Real.sqrt K₁
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (2 * Real.pi) * K * L,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK.le) hL, ?_⟩
  intro rsel hrsel z hz vs hvs v hvq
  let p := pairGrading (sectorGrading S) realGrading
  let A : ℝ := 1 + p (b + loss + d) z + ∑ i : Fin n, p (b + loss + d) (vs i)
  have hA : 0 ≤ A := add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
    (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  have hE : (∑' m, stateLocalizationEnergy D T C base (c + 1) v m) ≤
      ENNReal.ofReal (K₀ * (p (base + c + 6) v) ^ 2) := by
    have hi : base + (c + 1) + 5 = base + c + 6 := by omega
    exact (lowData.choose_spec.2 v).trans_eq
      (congrArg (fun i : ℕ => ENNReal.ofReal (K₀ * (p i v) ^ 2)) hi)
  have hF : (∑' m, stateLocalizationEnergy D T C (b + loss + d) (c + 1) v m) ≤
      ENNReal.ofReal (K₁ * (p (b + loss + d + c + 6) v) ^ 2) := by
    have hi : b + loss + d + (c + 1) + 5 = b + loss + d + c + 6 := by omega
    exact (highData.choose_spec.2 v).trans_eq
      (congrArg (fun i : ℕ => ENNReal.ofReal (K₁ * (p i v) ^ 2)) hi)
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  exact weightedJetNorm_le_scaled_two_envelopes
    hK.le hK₀ hK₁ hA (apply_nonneg _ _) (apply_nonneg _ _) hE hF
    (fun m => (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz (Fin.snoc vs v) m).1)
    hM hH b c (fun m θ => pointData.choose_spec.2 rsel hrsel z hz vs hvs v hvq m θ)

theorem N01Properties.endpointFlowScalarJets_state_weightedJetNorm_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n : ℕ) :
    ∃ d : ℕ, ∀ b c : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading base (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ, v.2 = 0 →
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss + d) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + loss + d) (vs i)) *
            pairGrading (sectorGrading S) realGrading (base + c + 6) v +
          pairGrading (sectorGrading S) realGrading (b + loss + d + c + 6) v) := by
  let lossData := hN.endpointFlowScalarJets_state_weightedJetNorm_bound_uniform_radius hS hT n
  let d : ℕ := lossData.choose
  let horders := lossData.choose_spec
  refine ⟨d, ?_⟩
  intro b c
  let data := horders b c
  exact ⟨data.choose, data.choose_spec.1, data.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
