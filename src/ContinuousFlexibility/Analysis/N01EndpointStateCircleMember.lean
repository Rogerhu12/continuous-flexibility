import ContinuousFlexibility.Analysis.N01EndpointWeightedJets
import ContinuousFlexibility.Analysis.N01StateLocalizationEnergy
import ContinuousFlexibility.Analysis.CircleEnergyEnvelope

/-!
# Actual endpoint jets with a state slot belong to the circle model

Only the distinguished direction is localized. The other directions
and the base point remain in their original physical spaces. The
resulting envelope is summable and depends quadratically on that one
direction, uniformly over the base point and the remaining slots.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointStateCircleMemberStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointStateCircleMemberRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_state_energy_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n s : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ (vs : Fin n → (StateDirections S × ℝ)) (v : StateDirections S × ℝ), v.2 = 0 →
      ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ| ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (max base (s + loss)) z) *
          (∏ i : Fin n, pairGrading (sectorGrading S) realGrading
            (max base (s + loss)) (vs i)) *
          Real.sqrt (stateLocalizationEnergy D T C (max base (s + loss)) (s + 1) v m).toReal := by
  obtain ⟨K, hK, hpoint⟩ := hN.endpointFlowScalarJets_weighted_bound hS hT rsel hrsel (n + 1) s
  let t : ℕ := max base (s + loss)
  let p := pairGrading (sectorGrading S) realGrading
  let L : ℝ := 1 + circleSingletonGradingConstant t * (2 * circleSobolevConstant)
  have hL : 0 < L := by
    have hnonneg := mul_nonneg (circleSingletonGradingConstant_nonneg t)
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) circleSobolevConstant_nonneg)
    dsimp only [L]
    linarith only [hnonneg]
  have hn : 0 < (n : ℝ) + 2 := by positivity
  refine ⟨K * ((n : ℝ) + 2) * L, mul_pos (mul_pos hK hn) hL, ?_⟩
  intro z hz vs v hvq
  obtain ⟨w, _, hlocal, henergy⟩ :=
    hN.exists_localized_state_energy_directions hS hT v hvq
  intro m b c horder θ
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM : 1 ≤ T.M (T.sample m) := (hT.2.1 _ hsample).2.2.2
  have hM0 : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  have heq :
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ =
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs (w m)) m) θ := by
    rw [hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1) z hz,
      hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel (n + 1) z hz]
    exact hlocal m n b θ (rsel m) (hrsel m)
      (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
        (hrsel m) b θ) z hz vs
  let A : ℝ := ((n : ℝ) + 2) * (1 + p t z) * ∏ i : Fin n, p t (vs i)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hn.le (add_nonneg zero_le_one (apply_nonneg _ _)))
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  have hprod : (∏ i : Fin (n + 1), p t (Fin.snoc vs (w m) i)) =
      (∏ i : Fin n, p t (vs i)) * p t (w m) := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hW : oneHighVariationWeight p base (s + loss) z (Fin.snoc vs (w m)) ≤
      A * p t (w m) := by
    have h := oneHighVariationWeight_le_seminorm_product p (p t) base (s + loss)
      (sectorPairGrading_monotone S (le_max_left _ _))
      (sectorPairGrading_monotone S (le_max_right _ _)) z (Fin.snoc vs (w m))
    rw [hprod] at h
    convert h using 1 <;> simp only [A, Nat.cast_add, Nat.cast_one] <;> ring
  have hc : T.M (T.sample m) ^ (c + 1) ≤ T.M (T.sample m) ^ (s + 1) :=
    pow_le_pow_right₀ hM (by omega)
  have hlocalweight : T.M (T.sample m) ^ (c + 1) * p t (w m) ≤
      L * Real.sqrt (stateLocalizationEnergy D T C t (s + 1) v m).toReal :=
    (mul_le_mul_of_nonneg_right hc (apply_nonneg _ _)).trans (henergy m t (s + 1))
  rw [heq]
  calc
    _ ≤ K * T.M (T.sample m) ^ (c + 1) *
        oneHighVariationWeight p base (s + loss) z (Fin.snoc vs (w m)) :=
      hpoint m b c θ (by omega) z hz (Fin.snoc vs (w m))
    _ ≤ K * T.M (T.sample m) ^ (c + 1) * (A * p t (w m)) :=
      mul_le_mul_of_nonneg_left hW (mul_nonneg hK.le (pow_nonneg hM0 _))
    _ = K * A * (T.M (T.sample m) ^ (c + 1) * p t (w m)) := by ring
    _ ≤ K * A * (L *
        Real.sqrt (stateLocalizationEnergy D T C t (s + 1) v m).toReal) :=
      mul_le_mul_of_nonneg_left hlocalweight (mul_nonneg hK.le hA)
    _ = _ := by dsimp only [A, L, t, p]; ring

theorem N01Properties.endpointFlowScalarJets_state_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (vs : Fin n → (StateDirections S × ℝ))
    (v : StateDirections S × ℝ) (hvq : v.2 = 0) :
    CircleMember T (3 / 4 : ℝ)
      (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) := by
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  apply circleMember_of_energy_envelope
    (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz (Fin.snoc vs v)) hM hH
  intro s
  obtain ⟨K, hK, hbound⟩ := hN.endpointFlowScalarJets_state_energy_bound hS hT rsel hrsel n s
  let t : ℕ := max base (s + loss)
  let p := pairGrading (sectorGrading S) realGrading
  refine ⟨stateLocalizationEnergy D T C t (s + 1) v,
    K * (1 + p t z) * ∏ i : Fin n, p t (vs i),
    hN.stateLocalizationEnergy_tsum_lt_top hS hT t (s + 1) v, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hK.le (add_nonneg zero_le_one (apply_nonneg _ _)))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  · exact hbound z hz vs v hvq

end ContinuousFlexibility.Statements
