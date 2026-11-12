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

private theorem abs_mul_le_of_mem_unit_interval
    {t q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |t * q| ≤ |q| := by
  rw [abs_mul, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (abs_nonneg _) ht.2

private theorem pair_grading_scaled_scalar_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (j : ℕ) (z : E × ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pairGrading p realGrading j (z.1, t * z.2) ≤
      pairGrading p realGrading j z := by
  change p j z.1 + ‖t * z.2‖ ≤ p j z.1 + ‖z.2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
  exact add_le_add (le_refl _) (mul_le_of_le_one_left (abs_nonneg _) ht.2)

private theorem hasDerivAt_mul_argument
    {f : ℝ → ℝ} {d t q : ℝ} (hf : HasDerivAt f d (t * q)) :
    HasDerivAt (fun a => f (a * q)) (q * d) t := by
  simpa only [Function.comp_def] using
    (hf.comp t (hasDerivAt_mul_const q)).congr_deriv (mul_comm d q)

private theorem scalar_height_curve_energy_bound
    {q M K A B lo hi p y : ℝ} {E : ℝ≥0∞}
    (c s : ℕ) (hM : 1 ≤ M) (hcs : c ≤ s)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 2 + B ≤ A)
    (hlo : 0 ≤ lo) (hloE : lo ≤ Real.sqrt E.toReal)
    (hhiE : hi ≤ Real.sqrt E.toReal)
    (hpoint : p * |y| ≤ K * M ^ (c + 1) * ((((0 : ℕ) : ℝ) + 2 + B) * lo + hi)) :
    p * |q * y| ≤ |q| * K * (A + 1) *
      Real.sqrt (ENNReal.ofReal ((M ^ (s + 1)) ^ 2) * E).toReal := by
  let e : ℝ := Real.sqrt E.toReal
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hW : (2 + B) * lo + hi ≤ (A + 1) * e := by
    calc
      (2 + B) * lo + hi ≤ A * lo + hi :=
        add_le_add (mul_le_mul_of_nonneg_right hB hlo) (le_refl _)
      _ ≤ A * e + e := add_le_add (mul_le_mul_of_nonneg_left hloE hA) hhiE
      _ = (A + 1) * e := by ring
  have hp : p * |y| ≤ K * M ^ (c + 1) * ((2 + B) * lo + hi) := by
    simpa only [Nat.cast_zero, zero_add] using hpoint
  have hc : M ^ (c + 1) ≤ M ^ (s + 1) :=
    pow_le_pow_right₀ hM (by omega)
  have hsqrt : Real.sqrt (ENNReal.ofReal ((M ^ (s + 1)) ^ 2) * E).toReal =
      M ^ (s + 1) * e := by
    dsimp only [e]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (zero_le_one.trans hM) _)]
  calc
    p * |q * y| = |q| * (p * |y|) := by rw [abs_mul]; ring
    _ ≤ |q| * (K * M ^ (c + 1) * ((2 + B) * lo + hi)) :=
      mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ ≤ |q| * (K * M ^ (c + 1) * ((A + 1) * e)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hW
          (mul_nonneg hK (pow_nonneg (zero_le_one.trans hM) _))) (abs_nonneg _)
    _ ≤ |q| * (K * M ^ (s + 1) * ((A + 1) * e)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hK)
          (mul_nonneg (add_nonneg hA zero_le_one) he)) (abs_nonneg _)
    _ = |q| * K * (A + 1) *
        Real.sqrt (ENNReal.ofReal ((M ^ (s + 1)) ^ 2) * E).toReal := by
      rw [hsqrt]
      ring

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
  have habs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |t * z.2| ≤ |z.2| :=
    abs_mul_le_of_mem_unit_interval (q := z.2) ht
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      path t ∈ sectorNeighborhood S base ε ε :=
    (congrArg (fun x : StateDirections S × ℝ => x ∈ sectorNeighborhood S base ε ε)
      (hpath_eq t)).mpr ⟨hz.1, (habs t ht).trans_lt hz.2⟩
  have hgrade (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      pairGrading (sectorGrading S) realGrading j (path t) ≤
        pairGrading (sectorGrading S) realGrading j z :=
    (congrArg (pairGrading (sectorGrading S) realGrading j) (hpath_eq t)).trans_le
      (pair_grading_scaled_scalar_le (sectorGrading S) j z ht)
  let F : ℝ → ℕ → ℝ → ℝ := fun t =>
    hN.endpointFlowScalarJets hS hT rsel hrsel 0 (path t) Fin.elim0
  let G : ℝ → ℕ → ℕ → ℝ → ℝ := fun t m b θ =>
    z.2 * iteratedDeriv b
      (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (path t) (fun _ => scalarParameterDirection S) m) θ
  have htuple : Fin.cons (scalarParameterDirection S)
      (Fin.elim0 : Fin 0 → (StateDirections S × ℝ)) =
      (fun _ : Fin 1 => scalarParameterDirection S) := by
    funext i
    have hi : i = 0 := Fin.ext (by have hiLt := i.isLt; omega)
    subst i
    simp only [Fin.cons_zero]
  have hderiv (m b : ℕ) (θ t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun a => iteratedDeriv b (F a m) θ) (G t m b θ) t := by
    have hd := hN.endpointFlowScalarJets_hasDerivAt_line hS hT rsel hrsel 0 z₀
      (scalarParameterDirection S) Fin.elim0 (t * z.2) (hpath t ht) m b θ
    have heq : iteratedDeriv b
        (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (path t)
          (Fin.cons (scalarParameterDirection S)
            (Fin.elim0 : Fin 0 → (StateDirections S × ℝ))) m) θ =
        iteratedDeriv b
          (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (path t)
            (fun _ => scalarParameterDirection S) m) θ :=
      congrArg (fun v : Fin 1 → (StateDirections S × ℝ) =>
        iteratedDeriv b (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (path t) v m) θ) htuple
    exact hasDerivAt_mul_argument (t := t) (q := z.2) (hd.congr_deriv heq)
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
    have hbase : heightPairGrading S base (η m) ≤ e :=
      (hmono (le_max_left _ _) (η m)).trans ((directions.choose_spec.2.2.2 j).2 m)
    have hhigh : heightPairGrading S (s + loss) (η m) ≤ e :=
      (hmono (le_max_right _ _) (η m)).trans ((directions.choose_spec.2.2.2 j).2 m)
    have hη : ∃ a : ℝ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S (η m) (r, ψ) = stateU S (liftSectorParameter S C (path t)).1 (r, ψ) + a := by
      obtain ⟨a, ha⟩ := directions.choose_spec.2.2.1 m
      refine ⟨a, fun r hr ψ => ?_⟩
      exact (ha r hr ψ).trans
        (congrArg (fun x : StateDirections S × ℝ =>
          stateU S (liftSectorParameter S C x).1 (r, ψ) + a) (hpath_eq t)).symm
    exact scalar_height_curve_energy_bound c s (hM m) (by omega) hK.le hA
      (add_le_add (le_refl 2) (hgrade (s + loss) t ht))
      (apply_nonneg _ _) hbase hhigh
      (pointData.choose_spec.2 m b c θ (by omega) (path t) (hpath t ht) (η m) hη)
  have hp1 : path 1 = z :=
    (hpath_eq 1).trans (congrArg (fun q : ℝ => (z.1, q)) (one_mul z.2))
  have hp0 : path 0 = z₀ :=
    (hpath_eq 0).trans (congrArg (fun q : ℝ => (z.1, q)) (zero_mul z.2))
  have heq : (fun m θ => F 1 m θ - F 0 m θ) =
      (fun m θ => hN.endpointFlowScalarJets hS hT rsel hrsel 0 z Fin.elim0 m θ -
        hN.endpointFlowScalarJets hS hT rsel hrsel 0 (z.1, 0) Fin.elim0 m θ) :=
    congrArg₂ (fun f g : ℕ → ℝ → ℝ => fun m θ => f m θ - g m θ)
      (congrArg (fun x : StateDirections S × ℝ =>
        hN.endpointFlowScalarJets hS hT rsel hrsel 0 x Fin.elim0) hp1)
      (congrArg (fun x : StateDirections S × ℝ =>
        hN.endpointFlowScalarJets hS hT rsel hrsel 0 x Fin.elim0) hp0)
  exact (congrArg (CircleMember T (3 / 4 : ℝ)) heq).mp hmem

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
  exact (congrArg (fun f : ℕ → ℝ → ℝ => f ∈ P) heq).mp (P.add_mem hq hs)

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
    have hv : v = Fin.elim0 := by
      funext i
      exact Fin.elim0 i
    exact (congrArg (fun w : Fin 0 → (StateDirections S × ℝ) =>
      CircleMember T (3 / 4 : ℝ) (hN.endpointFlowScalarJets hS hT rsel hrsel 0 z w)) hv).mpr
      (hN.endpointFlowScalarJets_zero_circleMember hS hT rsel hrsel z hz)
  | succ n => exact hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz v

end ContinuousFlexibility.Statements
