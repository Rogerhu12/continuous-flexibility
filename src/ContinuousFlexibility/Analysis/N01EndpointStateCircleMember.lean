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

private theorem oneHigh_snoc_le_product
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    {n base high t : ℕ} (hbase : base ≤ t) (hhigh : high ≤ t)
    (z : E) (vs : Fin n → E) (w : E) :
    oneHighVariationWeight p base high z (Fin.snoc vs w) ≤
      ((n : ℝ) + 2) * ((1 + p t z) * ∏ i : Fin n, p t (vs i)) * p t w := by
  have h := oneHighVariationWeight_le_seminorm_product p (p t) base high
    (hp hbase) (hp hhigh) z (Fin.snoc vs w)
  have hprod : (∏ i : Fin (n + 1), p t ((Fin.snoc vs w : Fin (n + 1) → E) i)) =
      (∏ i : Fin n, p t (vs i)) * p t w := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hprod] at h
  convert h using 1 <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring

private theorem localized_energy_transfer
    {K M G R W q L e X : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hX : X ≤ K * M * W) (hW : W ≤ G * R * q)
    (henergy : M * q ≤ L * e) :
    X ≤ (K * G * L) * R * e := by
  calc
    X ≤ K * M * (G * R * q) :=
      hX.trans (mul_le_mul_of_nonneg_left hW (mul_nonneg hK hM))
    _ = K * G * R * (M * q) := by ring
    _ ≤ K * G * R * (L * e) :=
      mul_le_mul_of_nonneg_left henergy (mul_nonneg (mul_nonneg hK hG) hR)
    _ = _ := by ring

private theorem circleMember_of_seminorm_energy_envelope
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ} {n : ℕ}
    (hu : ∀ m, ContDiff ℝ ∞ (u m) ∧ Function.Periodic (u m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (p : ℕ → Seminorm ℝ E) (order : ℕ → ℕ) (z : E) (vs : Fin n → E)
    (energy : ℕ → ℕ → ℝ≥0∞) (henergy : ∀ s, (∑' m, energy s m) < ⊤)
    (hpoint : ∀ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (u m) θ| ≤ K * (1 + p (order s) z) *
          (∏ i : Fin n, p (order s) (vs i)) * Real.sqrt (energy s m).toReal) :
    CircleMember T γ u := by
  apply circleMember_of_energy_envelope hu hM hH
  intro s
  obtain ⟨K, hK, hb⟩ := hpoint s
  refine ⟨energy s, K * (1 + p (order s) z) * ∏ i : Fin n, p (order s) (vs i),
    henergy s, ?_, hb⟩
  exact mul_nonneg (mul_nonneg hK (add_nonneg zero_le_one (apply_nonneg _ _)))
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))

theorem N01Properties.endpointFlowScalarJets_state_energy_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) (n : ℕ) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ (vs : Fin n → (StateDirections S × ℝ)) (v : StateDirections S × ℝ), v.2 = 0 →
      ∀ m b c, b + c ≤ s → ∀ θ,
      (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
        |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ| ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (max base (s + loss + d)) z) *
          (∏ i : Fin n, pairGrading (sectorGrading S) realGrading
            (max base (s + loss + d)) (vs i)) *
          Real.sqrt (stateLocalizationEnergy D T C (max base (s + loss + d)) (s + 1) v m).toReal := by
  let lossData := hN.endpointFlowScalarJets_weighted_bound hS hT rsel hrsel (n + 1)
  let d : ℕ := lossData.choose
  let horders := lossData.choose_spec
  refine ⟨d, ?_⟩
  intro s
  let pointData := horders s
  let K : ℝ := pointData.choose
  have hK : 0 < K := pointData.choose_spec.1
  let t : ℕ := max base (s + loss + d)
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
  let localData := hN.exists_localized_state_energy_directions hS hT v hvq
  let w : ℕ → (StateDirections S × ℝ) := localData.choose
  intro m b c horder θ
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM : 1 ≤ T.M (T.sample m) := (hT.2.1 _ hsample).2.2.2
  have hM0 : 0 ≤ T.M (T.sample m) := zero_le_one.trans hM
  have heq :
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v) m) θ =
      iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs (w m)) m) θ := by
    exact (hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel
      (n + 1) z hz (Fin.snoc vs v) m b θ).trans
        ((localData.choose_spec.2.1 m n b θ (rsel m) (hrsel m)
          (hN.sectorFlow_closed_angularTower hS hT m (rsel m)
            (hrsel m) b θ) z hz vs).trans
          (hN.endpointFlowScalarJets_iteratedDeriv hS hT rsel hrsel
            (n + 1) z hz (Fin.snoc vs (w m)) m b θ).symm)
  let A : ℝ := (1 + p t z) * ∏ i : Fin n, p t (vs i)
  have hA : 0 ≤ A := mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  have hW : oneHighVariationWeight p base (s + loss + d) z (Fin.snoc vs (w m)) ≤
      ((n : ℝ) + 2) * A * p t (w m) :=
    oneHigh_snoc_le_product p (sectorPairGrading_monotone S)
      (le_max_left _ _) (le_max_right _ _) z vs (w m)
  have hc : T.M (T.sample m) ^ (c + 1) ≤ T.M (T.sample m) ^ (s + 1) :=
    pow_le_pow_right₀ hM (by omega)
  have hlocalweight : T.M (T.sample m) ^ (c + 1) * p t (w m) ≤
      L * Real.sqrt (stateLocalizationEnergy D T C t (s + 1) v m).toReal :=
    (mul_le_mul_of_nonneg_right hc (apply_nonneg _ _)).trans
      (localData.choose_spec.2.2 m t (s + 1))
  have hlocalized := localized_energy_transfer hK.le (pow_nonneg hM0 (c + 1)) hn.le hA
    (pointData.choose_spec.2 m b c θ (by omega) z hz (Fin.snoc vs (w m))) hW hlocalweight
  have hweighted := congrArg (fun x : ℝ =>
    (T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) * |x|) heq
  exact hweighted.trans_le (by simpa only [A, mul_assoc] using hlocalized)

theorem N01Properties.endpointFlowScalarJets_state_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (vs : Fin n → (StateDirections S × ℝ))
    (v : StateDirections S × ℝ) (hvq : v.2 = 0) :
    CircleMember T (3 / 4 : ℝ)
      (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) := by
  let lossData := hN.endpointFlowScalarJets_state_energy_bound hS hT rsel hrsel n
  let d : ℕ := lossData.choose
  let horders := lossData.choose_spec
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  apply circleMember_of_seminorm_energy_envelope
    (hN.endpointFlowScalarJets_regular hS hT rsel hrsel (n + 1) z hz (Fin.snoc vs v)) hM hH
    (pairGrading (sectorGrading S) realGrading) (fun s => max base (s + loss + d)) z vs
    (fun s => stateLocalizationEnergy D T C (max base (s + loss + d)) (s + 1) v)
    (fun s => hN.stateLocalizationEnergy_tsum_lt_top hS hT (max base (s + loss + d)) (s + 1) v)
  intro s
  let data := horders s
  exact ⟨data.choose, data.choose_spec.1.le, data.choose_spec.2 z hz vs v hvq⟩

end ContinuousFlexibility.Statements
