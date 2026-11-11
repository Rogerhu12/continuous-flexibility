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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

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
  obtain ⟨K, hK, hpoint⟩ := hN.endpointFlowScalarJets_state_split_energy_bound hS hT rsel hrsel n b c
  obtain ⟨K₀, hK₀, hE₀⟩ := hN.stateLocalizationEnergy_tsum_le_grading_sq hS hT base (c + 1)
  obtain ⟨K₁, hK₁, hE₁⟩ := hN.stateLocalizationEnergy_tsum_le_grading_sq hS hT (b + loss) (c + 1)
  let L : ℝ := Real.sqrt K₀ + Real.sqrt K₁
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (2 * Real.pi) * K * L,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK.le) hL, ?_⟩
  intro z hz vs hvs v hvq
  let p := pairGrading (sectorGrading S) realGrading
  let A : ℝ := 1 + p (b + loss) z + ∑ i : Fin n, p (b + loss) (vs i)
  have hA : 0 ≤ A := add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
    (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  let U : ℝ := Real.sqrt K₀ * p (base + c + 6) v
  let V : ℝ := Real.sqrt K₁ * p (b + loss + c + 6) v
  have hU : 0 ≤ U := mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hV : 0 ≤ V := mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hE : (∑' m, stateLocalizationEnergy D T C base (c + 1) v m) ≤
      ENNReal.ofReal (U ^ 2) := by
    dsimp only [U]
    rw [mul_pow, Real.sq_sqrt hK₀]
    have hi : base + (c + 1) + 5 = base + c + 6 := by omega
    simpa only [hi] using hE₀ v
  have hF : (∑' m, stateLocalizationEnergy D T C (b + loss) (c + 1) v m) ≤
      ENNReal.ofReal (V ^ 2) := by
    dsimp only [V]
    rw [mul_pow, Real.sq_sqrt hK₁]
    have hi : b + loss + (c + 1) + 5 = b + loss + c + 6 := by omega
    simpa only [hi] using hE₁ v
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  have hn := circleWeightedJetNorm_le_two_envelopes
    (mul_nonneg hK.le hA) hK.le hU hV hE hF
    (fun m => (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz (Fin.snoc vs v) m).1)
    hM hH b c (fun m θ => (hpoint z hz vs hvs v hvq m θ).trans_eq (by
      dsimp only [A, p]
      ring))
  have h₀ : Real.sqrt K₀ ≤ L := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have h₁ : Real.sqrt K₁ ≤ L := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  calc
    circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        Real.sqrt (2 * Real.pi) * (K * A * U + K * V) := hn
    _ = Real.sqrt (2 * Real.pi) * K *
        (A * (Real.sqrt K₀ * p (base + c + 6) v) +
          Real.sqrt K₁ * p (b + loss + c + 6) v) := by dsimp only [U, V]; ring
    _ ≤ Real.sqrt (2 * Real.pi) * K *
        (A * (L * p (base + c + 6) v) + L * p (b + loss + c + 6) v) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h₀ (apply_nonneg _ _)) hA)
          (mul_le_mul_of_nonneg_right h₁ (apply_nonneg _ _)))
        (mul_nonneg (Real.sqrt_nonneg _) hK.le)
    _ = _ := by dsimp only [A, p]; ring

end ContinuousFlexibility.Statements
