import ContinuousFlexibility.Analysis.N01EndpointStateJetGrowth
import ContinuousFlexibility.Analysis.N01EndpointScalarJetGrowth
import ContinuousFlexibility.Analysis.CircleMultilinearRealization

/-!
# Fixed-loss local circle estimates for every positive endpoint jet

The genuine multilinear jet is split into its pure scalar part and a
finite sum with one state slot. The exact decoder realizes this identity
in each Hilbert coordinate, where the triangle inequality applies.
One low order and one loss work for every parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointJetLocalGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem endpointJet_scalar_part_pairGrading_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (j : ℕ) (v : E × ℝ) :
    pairGrading p realGrading j (v.2 • ((0 : E), (1 : ℝ))) ≤
      pairGrading p realGrading j v := by
  change p j (v.2 • (0 : E)) + ‖v.2 * 1‖ ≤ p j v.1 + ‖v.2‖
  have hzero : p j (0 : E) = 0 := (p j).map_zero'
  simp only [smul_zero, hzero, zero_add, mul_one]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

private theorem endpointJet_state_part_pairGrading_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (j : ℕ) (v : E × ℝ) :
    pairGrading p realGrading j (v - v.2 • ((0 : E), (1 : ℝ))) ≤
      pairGrading p realGrading j v := by
  have heq : v - v.2 • ((0 : E), (1 : ℝ)) = (v.1, (0 : ℝ)) := by
    apply Prod.ext
    · change v.1 - v.2 • (0 : E) = v.1
      rw [smul_zero, sub_zero]
    · change v.2 - v.2 * 1 = 0
      rw [mul_one, sub_self]
  rw [heq]
  change p j v.1 + ‖(0 : ℝ)‖ ≤ p j v.1 + ‖v.2‖
  rw [norm_zero, add_zero]
  exact le_add_of_nonneg_right (norm_nonneg _)

private theorem endpointJet_scalar_split_diagonal_snd
    {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (u : E × ℝ) (hu : u.2 = 1) (v : Fin k → E × ℝ) (i : Fin k) :
    (multilinearDifferenceTuple (fun j => (v j).2 • u) v i i).2 = 0 := by
  simp only [multilinearDifferenceTuple, lt_self_iff_false, if_false, if_true]
  change (v i).2 - (v i).2 * u.2 = 0
  rw [hu, mul_one, sub_self]

theorem sectorParameter_scalarPart_grading_le
    (S : PhysicalSpacesData) (j : ℕ) (v : StateDirections S × ℝ) :
    pairGrading (sectorGrading S) realGrading j (v.2 • scalarParameterDirection S) ≤
      pairGrading (sectorGrading S) realGrading j v := by
  exact endpointJet_scalar_part_pairGrading_le
    (E := StateDirections S) (sectorGrading S) j v

theorem sectorParameter_statePart_grading_le
    (S : PhysicalSpacesData) (j : ℕ) (v : StateDirections S × ℝ) :
    pairGrading (sectorGrading S) realGrading j (v - v.2 • scalarParameterDirection S) ≤
      pairGrading (sectorGrading S) realGrading j v := by
  exact endpointJet_state_part_pairGrading_le
    (E := StateDirections S) (sectorGrading S) j v

private theorem endpointJet_mixed_norm_bound
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin k => E) F) (v q : Fin k → E)
    (Kq Ks Q : ℝ) (hq : ‖A q‖ ≤ Kq * Q)
    (hterm : ∀ i : Fin k, ‖A (multilinearDifferenceTuple q v i)‖ ≤ Ks * Q) :
    ‖A v‖ ≤ (Kq + (k : ℝ) * Ks) * Q := by
  classical
  have hidentity : A v = A q + ∑ i : Fin k, A (multilinearDifferenceTuple q v i) := by
    have heq : A v - A q = ∑ i : Fin k, A (multilinearDifferenceTuple q v i) := by
      change A v - A q = ∑ i : Fin k,
        A (fun j => if j < i then v j else if i = j then v j - q j else q j)
      simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies] using
        A.map_sub_map_piecewise v q Finset.univ
    calc
      A v = A q + (A v - A q) := by abel
      _ = _ := congrArg (fun y : F => A q + y) heq
  calc
    ‖A v‖ ≤ ‖A q‖ + ∑ i : Fin k, ‖A (multilinearDifferenceTuple q v i)‖ := by
      rw [hidentity]
      exact (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ Kq * Q + ∑ _i : Fin k, Ks * Q :=
      add_le_add hq (Finset.sum_le_sum (fun i _ => hterm i))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_positive_circleNorm_local_growth_uniform_radius
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (v i) ≤ 1) →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin (n + 1), pairGrading (sectorGrading S) realGrading (s + L) (v i)) := by
  classical
  let stateData := hN.endpointFlowScalarJets_state_slot_circleNorm_local_growth_all_uniform_radius hS hT
  let Bₛ : ℕ := stateData.choose
  let Lₛ : ℕ := stateData.choose_spec.choose
  have hBₛ : base ≤ Bₛ := stateData.choose_spec.choose_spec.1
  let scalarData := hN.endpointFlow_pure_scalar_circleNorm_local_growth_all_uniform_radius hS hT
  let Bq : ℕ := scalarData.choose
  let Lq : ℕ := scalarData.choose_spec.choose
  let B : ℕ := max Bₛ Bq
  let L : ℕ := max Lₛ Lq
  have hBs : Bₛ ≤ B := le_max_left _ _
  have hBq : Bq ≤ B := le_max_right _ _
  have hLs : Lₛ ≤ L := le_max_left _ _
  have hLq : Lq ≤ L := le_max_right _ _
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  refine ⟨B, L, hBₛ.trans hBs, ?_⟩
  intro n R hR s hs
  let stateOrder := stateData.choose_spec.choose_spec.2 n R hR s (hBs.trans hs)
  let Ks : ℝ := stateOrder.choose
  have hKs : 0 ≤ Ks := stateOrder.choose_spec.1
  let scalarOrder := scalarData.choose_spec.choose_spec.2 n R hR s (hBq.trans hs)
  let Kq : ℝ := scalarOrder.choose
  have hKq : 0 ≤ Kq := scalarOrder.choose_spec.1
  refine ⟨Kq + ((n + 1 : ℕ) : ℝ) * Ks,
    add_nonneg hKq (mul_nonneg (Nat.cast_nonneg _) hKs), ?_⟩
  intro rsel hrsel z hz hzb v hv
  let q : Fin (n + 1) → (StateDirections S × ℝ) :=
    fun i => (v i).2 • scalarParameterDirection S
  let A := hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z
  let M := liftCircleMultilinear (hS.2.1 (3 / 4 : ℝ)) A
    (hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz)
  let coordinate := projectiveCoordinate
    (fun j => (S.circle (3 / 4 : ℝ)).level j) (S.circle (3 / 4 : ℝ)).bond s
  let F := coordinate.toLinearMap.compMultilinearMap M
  have hnorm (w : Fin (n + 1) → (StateDirections S × ℝ)) :
      ‖F w‖ = circleNorm T (3 / 4 : ℝ) s (A w) := by
    have hlevel : ‖(M w).val s‖ =
        circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode (M w)) :=
      (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2 (M w) s
    have hdecode : (S.circle (3 / 4 : ℝ)).decode (M w) = A w :=
      liftCircleMultilinear_decode (hS.2.1 (3 / 4 : ℝ)) A
        (hN.endpointFlowScalarJets_positive_circleMember hS hT rsel hrsel n z hz) w
    exact (show ‖F w‖ = ‖(M w).val s‖ from rfl).trans
      (hlevel.trans (congrArg (circleNorm T (3 / 4 : ℝ) s) hdecode))
  let Q : ℝ := 1 + p (s + L) z + ∑ i : Fin (n + 1), p (s + L) (v i)
  have hsum0 : 0 ≤ ∑ i : Fin (n + 1), p (s + L) (v i) :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hqp : ‖F q‖ ≤ Kq * Q := by
    have heq : F q = (∏ i : Fin (n + 1), (v i).2) •
        F (fun _ => scalarParameterDirection S) :=
      F.map_smul_univ (fun i => (v i).2) (fun _ => scalarParameterDirection S)
    have hcoeff (i : Fin (n + 1)) : |(v i).2| ≤ 1 := by
      have h := (sectorParameter_scalarPart_grading_le S B (v i)).trans (hv i)
      simpa only [map_smul_eq_mul, scalarParameterDirection_grading,
        Real.norm_eq_abs, mul_one] using h
    have hprod : |∏ i : Fin (n + 1), (v i).2| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hcoeff i)
    have hhigh : p (s + Lq) z ≤ p (s + L) z := hp (by omega) z
    calc
      ‖F q‖ = |∏ i : Fin (n + 1), (v i).2| * ‖F (fun _ => scalarParameterDirection S)‖ :=
        (congrArg (fun y : (S.circle (3 / 4 : ℝ)).level s => ‖y‖) heq).trans
          (by simpa only [Real.norm_eq_abs] using
            norm_smul (∏ i : Fin (n + 1), (v i).2) (F (fun _ => scalarParameterDirection S)))
      _ ≤ ‖F (fun _ => scalarParameterDirection S)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hprod
      _ ≤ Kq * (1 + p (s + Lq) z) :=
        (hnorm (fun _ => scalarParameterDirection S)).trans_le
          (scalarOrder.choose_spec.2 rsel hrsel z hz ((hp hBq z).trans hzb))
      _ ≤ Kq * Q := mul_le_mul_of_nonneg_left
        (by dsimp only [Q]; linarith only [hhigh, hsum0]) hKq
  have hterm (i : Fin (n + 1)) :
      ‖F (multilinearDifferenceTuple q v i)‖ ≤ Ks * Q := by
    let w := multilinearDifferenceTuple q v i
    have hwgrade (j : ℕ) (a : Fin (n + 1)) : p j (w a) ≤ p j (v a) := by
      dsimp only [w, multilinearDifferenceTuple]
      split_ifs with h₀ h₁
      · exact le_rfl
      · subst a
        exact sectorParameter_statePart_grading_le S j (v i)
      · exact sectorParameter_scalarPart_grading_le S j (v a)
    have hwlow (a : Fin (n + 1)) : p Bₛ (w a) ≤ 1 :=
      (hwgrade Bₛ a).trans ((hp hBs (v a)).trans (hv a))
    have hwi : (w i).2 = 0 :=
      endpointJet_scalar_split_diagonal_snd (E := StateDirections S)
        (scalarParameterDirection S) rfl v i
    have hhigh : p (s + Lₛ) z ≤ p (s + L) z := hp (by omega) z
    have hsum : (∑ a : Fin (n + 1), p (s + Lₛ) (w a)) ≤
        ∑ a : Fin (n + 1), p (s + L) (v a) :=
      Finset.sum_le_sum (fun a _ => (hwgrade (s + Lₛ) a).trans (hp (by omega) (v a)))
    exact (hnorm w).trans_le
      ((stateOrder.choose_spec.2 rsel hrsel z hz ((hp hBs z).trans hzb) w hwlow ⟨i, hwi⟩).trans
        (mul_le_mul_of_nonneg_left
          (by dsimp only [Q]; linarith only [hhigh, hsum]) hKs))
  exact (hnorm v).symm.trans_le (endpointJet_mixed_norm_bound F v q Kq Ks Q hqp hterm)

theorem N01Properties.endpointFlowScalarJets_positive_circleNorm_local_growth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (v i) ≤ 1) →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin (n + 1), pairGrading (sectorGrading S) realGrading (s + L) (v i)) := by
  let data := hN.endpointFlowScalarJets_positive_circleNorm_local_growth_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  exact ⟨orderData.choose, orderData.choose_spec.1, orderData.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
