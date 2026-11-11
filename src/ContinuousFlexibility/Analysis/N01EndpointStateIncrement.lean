import ContinuousFlexibility.Analysis.N01EndpointStateCircleMember
import ContinuousFlexibility.Analysis.CircleCurveEnergyEnvelope

/-!
# The actual zero-scalar endpoint increment is a circle field

The state varies on the straight segment with scalar parameter zero.
A fixed localized state direction supplies the summable energy for the
whole segment, and the scalar mean value theorem controls every angular
jet of the actual endpoint difference.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointStateIncrementStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointStateIncrementRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem endpoint_origin_mem
    (hN : N01Properties D T S C base loss ε) :
    (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
  constructor
  · change sectorGrading S base (0 : StateDirections S) < ε
    have hzero : sectorGrading S base (0 : StateDirections S) = (0 : ℝ) :=
      (sectorGrading S base).map_zero'
    exact hzero.trans_lt hN.2.1
  · change |(0 : ℝ)| < ε
    rw [abs_zero]
    exact hN.2.1

theorem N01Properties.endpointFlowScalarJets_zero_at_origin
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    hN.endpointFlowScalarJets hS hT rsel hrsel 0 0 Fin.elim0 = 0 := by
  have href : liftSectorParameter S C (0 : StateDirections S × ℝ) =
      (C.referenceState, 0) := by
    apply Prod.ext
    · change C.referenceState + (0 : AnnularState S) = C.referenceState
      exact add_zero _
    · rfl
  funext m θ
  have h := hN.endpointFlowScalarJets_zero hS hT rsel hrsel 0 (endpoint_origin_mem hN) m θ
  simpa only [href, sub_self, Pi.zero_apply] using h

theorem N01Properties.endpointFlowScalarJets_state_increment_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    CircleMember T (3 / 4 : ℝ)
      (hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0) := by
  let u : StateDirections S × ℝ := (z.1, 0)
  have hu : u ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base z.1 < ε
      exact hz.1
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hN.2.1
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      t • u ∈ sectorNeighborhood S base ε ε := by
    have hm := sectorNeighborhood_convex S base ε ε (endpoint_origin_mem hN) hu
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_zero, zero_add] using hm
  let F : ℝ → ℕ → ℝ → ℝ := fun t =>
    hN.endpointFlowScalarJets hS hT rsel hrsel 0 (t • u) Fin.elim0
  let G : ℝ → ℕ → ℕ → ℝ → ℝ := fun t m b θ =>
    iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (t • u)
      (Fin.snoc (Fin.elim0 : Fin 0 → (StateDirections S × ℝ)) u :
        Fin 1 → (StateDirections S × ℝ)) m) θ
  have htuple :
      (Fin.cons u (Fin.elim0 : Fin 0 → (StateDirections S × ℝ)) :
        Fin 1 → (StateDirections S × ℝ)) =
      (Fin.snoc (Fin.elim0 : Fin 0 → (StateDirections S × ℝ)) u :
        Fin 1 → (StateDirections S × ℝ)) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  have hderiv (m b : ℕ) (θ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun a => iteratedDeriv b (F a m) θ) (G t m b θ) t := by
    have hm : (0 : StateDirections S × ℝ) + t • u ∈ sectorNeighborhood S base ε ε := by
      simpa only [zero_add] using hpath t ht
    have hd := hN.endpointFlowScalarJets_hasDerivAt_line hS hT rsel hrsel 0 0 u Fin.elim0 t hm m b θ
    simpa only [F, G, zero_add, htuple] using hd
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 0 ≤ T.M (T.sample m) := zero_le_one.trans (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  have hmem : CircleMember T (3 / 4 : ℝ) (fun m θ => F 1 m θ - F 0 m θ) := by
    apply circleMember_sub_of_curve_energy_envelope F G
      (hN.endpointFlowScalarJets_regular hS hT rsel hrsel 0 (0 • u) (hpath 0 (by simp)) Fin.elim0)
      (hN.endpointFlowScalarJets_regular hS hT rsel hrsel 0 (1 • u) (hpath 1 (by simp)) Fin.elim0)
      hM hH hderiv
    intro s
    obtain ⟨K, hK, hbound⟩ := hN.endpointFlowScalarJets_state_energy_bound hS hT rsel hrsel 0 s
    let j : ℕ := max base (s + loss)
    let p := pairGrading (sectorGrading S) realGrading
    refine ⟨stateLocalizationEnergy D T C j (s + 1) u, K * (1 + p j u),
      hN.stateLocalizationEnergy_tsum_lt_top hS hT j (s + 1) u,
      mul_nonneg hK.le (add_nonneg zero_le_one (apply_nonneg _ _)), ?_⟩
    intro m b c hbc θ t ht
    have hgrade : p j (t • u) ≤ p j u := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (apply_nonneg _ _) ht.2
    have hb := hbound (t • u) (hpath t ht) Fin.elim0 u rfl m b c hbc θ
    simp only [Fin.prod_univ_zero, mul_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hgrade) hK.le)
      (Real.sqrt_nonneg _))
  have heq : (fun m θ => F 1 m θ - F 0 m θ) =
      hN.endpointFlowScalarJets hS hT rsel hrsel 0 u Fin.elim0 := by
    funext m θ
    simp only [F, one_smul, zero_smul, hN.endpointFlowScalarJets_zero_at_origin hS hT rsel hrsel,
      Pi.zero_apply, sub_zero]
  rw [heq] at hmem
  exact hmem

end ContinuousFlexibility.Statements
