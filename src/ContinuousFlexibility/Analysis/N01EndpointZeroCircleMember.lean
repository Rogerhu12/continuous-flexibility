import ContinuousFlexibility.Analysis.N01EndpointStateIncrement
import ContinuousFlexibility.Analysis.N01EndpointPositiveCircleMember

/-!
# The actual zero-order endpoint difference belongs to the circle model

First change the state with scalar parameter zero, then change only the
scalar parameter. The second segment has a fixed physical height, so
one summable plateau energy controls the entire segment. Both pieces
are differences of the actual endpoint fields.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointZeroCircleMemberStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointZeroCircleMemberRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.endpointFlowScalarJets_scalar_increment_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    CircleMember T (3 / 4 : ℝ) (fun m θ =>
      hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 m θ -
        hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0 m θ) := by
  let z₀ : StateDirections S × ℝ := (z.1, 0)
  let path : ℝ → (StateDirections S × ℝ) :=
    fun t => z₀ + (t * z.2) • scalarParameterDirection S
  have hpath_eq (t : ℝ) : path t = (z.1, t * z.2) :=
    scalarParameter_zero_line S z.1 (t * z.2)
  have habs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |t * z.2| ≤ |z.2| := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      path t ∈ sectorNeighborhood S base ε ε := by
    rw [hpath_eq]
    exact ⟨hz.1, (habs t ht).trans_lt hz.2⟩
  have hgrade (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      pairGrading (sectorGrading S) realGrading j (path t) ≤
        pairGrading (sectorGrading S) realGrading j z := by
    rw [hpath_eq]
    change sectorGrading S j z.1 + ‖t * z.2‖ ≤ sectorGrading S j z.1 + ‖z.2‖
    simpa only [Real.norm_eq_abs] using add_le_add (le_refl (sectorGrading S j z.1)) (habs t ht)
  let F : ℝ → ℕ → ℝ → ℝ := fun t =>
    hN.endpointFlowScalarJets hS hT rsel hrsel 0 (path t) Fin.elim0
  let G : ℝ → ℕ → ℕ → ℝ → ℝ := fun t m b θ =>
    z.2 * iteratedDeriv b
      (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (path t) (fun _ => scalarParameterDirection S) m) θ
  have htuple : Fin.cons (scalarParameterDirection S)
      (Fin.elim0 : Fin 0 → (StateDirections S × ℝ)) =
      (fun _ : Fin 1 => scalarParameterDirection S) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  have hderiv (m b : ℕ) (θ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun a => iteratedDeriv b (F a m) θ) (G t m b θ) t := by
    have hd := hN.endpointFlowScalarJets_hasDerivAt_line hS hT rsel hrsel 0 z₀
      (scalarParameterDirection S) Fin.elim0 (t * z.2) (hpath t ht) m b θ
    rw [htuple] at hd
    have h := hd.comp t ((hasDerivAt_id t).mul_const z.2)
    simpa only [F, G, path, Function.comp_def, mul_comm] using h
  let ξ : HeightPair S := (liftSectorParameter S C z).1.1
  let directions := hN.exists_height_pair_plateau_directions hS hT ξ
  let η : ℕ → HeightPair S := directions.choose
  have hmono : Monotone (heightPairGrading S) :=
    pairGrading_monotone
      (gradedSeminorm_monotone (fun i => (S.height (3 / 4 : ℝ)).level i)
        (S.height (3 / 4 : ℝ)).bond)
      (fun _ _ _ _ => le_rfl)
  have hs (m : ℕ) := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 m
  have hM (m : ℕ) : 1 ≤ T.M (T.sample m) := (hT.2.1 _ (hs m)).2.2.2
  have hH (m : ℕ) : 0 ≤ T.H (T.sample m) := (hT.2.1 _ (hs m)).2.1.le
  have hmem : CircleMember T (3 / 4 : ℝ) (fun m θ => F 1 m θ - F 0 m θ) := by
    apply circleMember_sub_of_curve_energy_envelope F G
      (hN.endpointFlowScalarJets_regular hS hT rsel hrsel 0 (path 0) (hpath 0 (by simp)) Fin.elim0)
      (hN.endpointFlowScalarJets_regular hS hT rsel hrsel 0 (path 1) (hpath 1 (by simp)) Fin.elim0)
      (fun m => zero_le_one.trans (hM m)) hH hderiv
    intro s
    let pointData := hN.endpointFlow_pure_scalar_weighted_height_bound hS hT rsel hrsel 0 s
    let K : ℝ := pointData.choose
    have hK : 0 < K := pointData.choose_spec.1
    let j : ℕ := max base (s + loss)
    let E : ℕ → ℝ≥0∞ := fun m =>
      ENNReal.ofReal ((T.M (T.sample m) ^ (s + 1)) ^ 2) *
        physicalPlateauEnergy D T C (3 / 4 : ℝ) j
          ((S.height (3 / 4 : ℝ)).decode ξ.1) m
    let A : ℝ := 2 + pairGrading (sectorGrading S) realGrading (s + loss) z
    have hA : 0 ≤ A := add_nonneg (by norm_num) (apply_nonneg _ _)
    refine ⟨E, |z.2| * K * (A + 1),
      hN.physicalPlateauEnergy_weighted_tsum_lt_top hS hT (hS.1 (3 / 4 : ℝ)) ξ.1 j (s + 1),
      mul_nonneg (mul_nonneg (abs_nonneg _) hK.le) (by positivity), ?_⟩
    intro m b c hbc θ t ht
    let e : ℝ := Real.sqrt (physicalPlateauEnergy D T C (3 / 4 : ℝ) j
      ((S.height (3 / 4 : ℝ)).decode ξ.1) m).toReal
    have he : 0 ≤ e := Real.sqrt_nonneg _
    have hbase : heightPairGrading S base (η m) ≤ e :=
      (hmono (le_max_left _ _) (η m)).trans ((directions.choose_spec.2.2.2 j).2 m)
    have hhigh : heightPairGrading S (s + loss) (η m) ≤ e :=
      (hmono (le_max_right _ _) (η m)).trans ((directions.choose_spec.2.2.2 j).2 m)
    have hη : ∃ a : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S (η m) (r, ψ) = stateU S (liftSectorParameter S C (path t)).1 (r, ψ) + a := by
      obtain ⟨a, ha⟩ := directions.choose_spec.2.2.1 m
      refine ⟨a, fun r hr ψ => ?_⟩
      rw [hpath_eq]
      exact ha r hr ψ
    let W : ℝ := (2 + pairGrading (sectorGrading S) realGrading (s + loss) (path t)) *
      heightPairGrading S base (η m) + heightPairGrading S (s + loss) (η m)
    have hW : W ≤ (A + 1) * e := by
      calc
        W ≤ A * heightPairGrading S base (η m) + heightPairGrading S (s + loss) (η m) :=
          add_le_add (mul_le_mul_of_nonneg_right
            (add_le_add (le_refl 2) (hgrade (s + loss) t ht)) (apply_nonneg _ _)) (le_refl _)
        _ ≤ A * e + e := add_le_add (mul_le_mul_of_nonneg_left hbase hA) hhigh
        _ = _ := by ring
    have hp := pointData.choose_spec.2 m b c θ (by omega) (path t) (hpath t ht) (η m) hη
    simp only [Nat.cast_zero, zero_add] at hp
    have hc : T.M (T.sample m) ^ (c + 1) ≤ T.M (T.sample m) ^ (s + 1) :=
      pow_le_pow_right₀ (hM m) (by omega)
    have hsqrt : Real.sqrt (E m).toReal = T.M (T.sample m) ^ (s + 1) * e := by
      dsimp only [E, e]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (zero_le_one.trans (hM m)) _)]
    calc
      _ = |z.2| * ((T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) *
          |iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (path t)
            (fun _ => scalarParameterDirection S) m) θ|) := by
        dsimp only [G]
        rw [abs_mul]
        ring
      _ ≤ |z.2| * (K * T.M (T.sample m) ^ (c + 1) * W) :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ ≤ |z.2| * (K * T.M (T.sample m) ^ (c + 1) * ((A + 1) * e)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hW
            (mul_nonneg hK.le (pow_nonneg (zero_le_one.trans (hM m)) _))) (abs_nonneg _)
      _ ≤ |z.2| * (K * T.M (T.sample m) ^ (s + 1) * ((A + 1) * e)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK.le)
            (mul_nonneg (by positivity) he)) (abs_nonneg _)
      _ = |z.2| * K * (A + 1) * Real.sqrt (E m).toReal := by rw [hsqrt]; ring
  have hp1 : path 1 = z := by
    rw [hpath_eq, one_mul]
  have hp0 : path 0 = z₀ := by
    rw [hpath_eq, zero_mul]
  simpa only [F, hp1, hp0, z₀] using hmem

theorem N01Properties.endpointFlowScalarJets_zero_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0) := by
  let P : Submodule ℝ (ℕ → ℝ → ℝ) := LinearMap.range (S.circle (3 / 4 : ℝ)).decode
  have hs : hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0 ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlowScalarJets_state_increment_circleMember hS hT rsel hrsel z hz)
  have hq : (fun m θ => hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 m θ -
      hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0 m θ) ∈ P :=
    (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mpr
      (hN.endpointFlowScalarJets_scalar_increment_circleMember hS hT rsel hrsel z hz)
  apply (circleDecode_mem_range_iff (hS.2.1 (3 / 4 : ℝ)) _).mp
  have heq : (fun m θ => hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 m θ -
        hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0 m θ) +
      hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0 =
      hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 := by
    funext m θ
    exact sub_add_cancel _ _
  simpa only [heq] using P.add_mem hq hs

/-- Every selected scalar jet, including its actual zero-order field,
belongs to the supplied physical circle model. -/
theorem N01Properties.endpointFlowScalarJets_circleMember
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m))
    (n : ℕ) (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → (StateDirections S × ℝ)) :
    CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel n z v) := by
  cases n with
  | zero =>
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    rw [hv]
    exact hN.endpointFlowScalarJets_zero_circleMember hS hT rsel hrsel z hz
  | succ n => exact hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz v

end ContinuousFlexibility.Statements
