import ContinuousFlexibility.Analysis.N01EndpointSplitEnergy
import ContinuousFlexibility.Analysis.CircleTwoEnergyEnvelope

/-!
# Actual endpoint estimates with the angular-material budget intact

This is a single weighted jet norm before the finite circle jet sum.
The low localized slot costs base+c+6, whereas the high localized slot
costs b+loss+c+6. The numerical constant is independent of the state and
all directions.
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

private theorem circleWeightedJetNorm_le_split_energy_bounds
    {T : MaterialData} {γ : ℝ} {f : ℕ → ℝ → ℝ}
    {E F : ℕ → ℝ≥0∞} {K A K₀ K₁ u v : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hE : (∑' m, E m) ≤ ENNReal.ofReal (K₀ * u ^ 2))
    (hF : (∑' m, F m) ≤ ENNReal.ofReal (K₁ * v ^ 2))
    (hf : ∀ m, ContDiff ℝ ∞ (f m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (b c : ℕ)
    (hpoint : ∀ m θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (f m) θ| ≤
      K * (A * Real.sqrt (E m).toReal + Real.sqrt (F m).toReal)) :
    circleWeightedJetNorm T γ b c f ≤
      (Real.sqrt (2 * Real.pi) * K * (Real.sqrt K₀ + Real.sqrt K₁)) * (A * u + v) := by
  let L : ℝ := Real.sqrt K₀ + Real.sqrt K₁
  have hE' : (∑' m, E m) ≤ ENNReal.ofReal ((Real.sqrt K₀ * u) ^ 2) := by
    simpa only [mul_pow, Real.sq_sqrt hK₀] using hE
  have hF' : (∑' m, F m) ≤ ENNReal.ofReal ((Real.sqrt K₁ * v) ^ 2) := by
    simpa only [mul_pow, Real.sq_sqrt hK₁] using hF
  have hn := circleWeightedJetNorm_le_two_envelopes
    (T := T) (γ := γ) (v := f) (E := E) (F := F)
    (A := K * A) (B := K) (U := Real.sqrt K₀ * u) (V := Real.sqrt K₁ * v)
    (mul_nonneg hK hA) hK
    (mul_nonneg (Real.sqrt_nonneg _) hu) (mul_nonneg (Real.sqrt_nonneg _) hv)
    hE' hF' hf hM hH b c
    (fun m θ => (hpoint m θ).trans_eq (by ring))
  have h₀ : Real.sqrt K₀ ≤ L := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have h₁ : Real.sqrt K₁ ≤ L := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  calc
    circleWeightedJetNorm T γ b c f ≤
        Real.sqrt (2 * Real.pi) *
          (K * A * (Real.sqrt K₀ * u) + K * (Real.sqrt K₁ * v)) := hn
    _ = Real.sqrt (2 * Real.pi) * K *
        (A * (Real.sqrt K₀ * u) + Real.sqrt K₁ * v) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * K * (A * (L * u) + L * v) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₀ hu) hA)
          (mul_le_mul_of_nonneg_right h₁ hv))
        (mul_nonneg (Real.sqrt_nonneg _) hK)
    _ = _ := by dsimp only [L]; ring

/-- The scaled two-envelope estimate, using the verified split-energy proof. -/
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
  exact circleWeightedJetNorm_le_split_energy_bounds
    (T := T) (γ := γ) (f := v) (E := E) (F := F)
    (K := K) (A := A) (K₀ := K₀) (K₁ := K₁) (u := u₀) (v := u₁)
    hK hA hK₀ hK₁ hu₀ hu₁ hE hF hv hM hH b c hpoint

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_state_weightedJetNorm_bound_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)), ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading base (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ, v.2 = 0 →
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + loss) (vs i)) *
            pairGrading (sectorGrading S) realGrading (base + c + 6) v +
          pairGrading (sectorGrading S) realGrading (b + loss + c + 6) v) := by
  let pointData := N01Properties.endpointFlowScalarJets_state_split_energy_bound_uniform_radius
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT n b c
  let K : ℝ := pointData.choose
  have hK : 0 < K := pointData.choose_spec.1
  let lowData := N01Properties.stateLocalizationEnergy_tsum_le_grading_sq
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT base (c + 1)
  let K₀ : ℝ := lowData.choose
  have hK₀ : 0 ≤ K₀ := lowData.choose_spec.1
  let highData := N01Properties.stateLocalizationEnergy_tsum_le_grading_sq
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT (b + loss) (c + 1)
  let K₁ : ℝ := highData.choose
  have hK₁ : 0 ≤ K₁ := highData.choose_spec.1
  let L : ℝ := Real.sqrt K₀ + Real.sqrt K₁
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (2 * Real.pi) * K * L,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK.le) hL, ?_⟩
  intro rsel hrsel z hz vs hvs v hvq
  let p := pairGrading (sectorGrading S) realGrading
  let A : ℝ := 1 + p (b + loss) z + ∑ i : Fin n, p (b + loss) (vs i)
  have hA : 0 ≤ A :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg (p (b + loss)) z))
      (Finset.sum_nonneg (fun i _ => apply_nonneg (p (b + loss)) (vs i)))
  have hlow : base + (c + 1) + 5 = base + c + 6 := by omega
  have hhigh : b + loss + (c + 1) + 5 = b + loss + c + 6 := by omega
  have hE : (∑' m, stateLocalizationEnergy D T C base (c + 1) v m) ≤
      ENNReal.ofReal (K₀ * (p (base + c + 6) v) ^ 2) :=
    (lowData.choose_spec.2 v).trans_eq
      (congrArg (fun k : ℕ => ENNReal.ofReal (K₀ * (p k v) ^ 2)) hlow)
  have hF : (∑' m, stateLocalizationEnergy D T C (b + loss) (c + 1) v m) ≤
      ENNReal.ofReal (K₁ * (p (b + loss + c + 6) v) ^ 2) :=
    (highData.choose_spec.2 v).trans_eq
      (congrArg (fun k : ℕ => ENNReal.ofReal (K₁ * (p k v) ^ 2)) hhigh)
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  exact circleWeightedJetNorm_le_split_energy_bounds
    (T := T) (γ := (3 / 4 : ℝ))
    (f := hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v))
    (E := stateLocalizationEnergy D T C base (c + 1) v)
    (F := stateLocalizationEnergy D T C (b + loss) (c + 1) v)
    (K := K) (A := A) (K₀ := K₀) (K₁ := K₁)
    (u := p (base + c + 6) v) (v := p (b + loss + c + 6) v)
    hK.le hA hK₀ hK₁
    (apply_nonneg (p (base + c + 6)) v)
    (apply_nonneg (p (b + loss + c + 6)) v) hE hF
    (fun m => (hN.endpointFlowScalarJets_regular hS hT rsel hrsel
      (n + 1) z hz (Fin.snoc vs v) m).1)
    hM hH b c (pointData.choose_spec.2 rsel hrsel z hz vs hvs v hvq)

theorem N01Properties.endpointFlowScalarJets_state_weightedJetNorm_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading base (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ, v.2 = 0 →
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * ((1 + pairGrading (sectorGrading S) realGrading (b + loss) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (b + loss) (vs i)) *
            pairGrading (sectorGrading S) realGrading (base + c + 6) v +
          pairGrading (sectorGrading S) realGrading (b + loss + c + 6) v) := by
  let data := N01Properties.endpointFlowScalarJets_state_weightedJetNorm_bound_uniform_radius
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
    hN hS hT n b c
  exact ⟨data.choose, data.choose_spec.1, data.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
