import ContinuousFlexibility.Analysis.N01EndpointSplitNorm
import ContinuousFlexibility.Analysis.N01EndpointPositiveCircleMember
import ContinuousFlexibility.Analysis.CircleWeightedJetNormSum
import ContinuousFlexibility.Analysis.LocalizedJetInterpolation
import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Fixed-loss local growth of actual endpoint jets with a state slot

The N01 angular order and the material order are added before
interpolation. The low order and loss are fixed before the size of the
base-point box and before the output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointStateJetGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

private theorem finite_sum_bound_by_card
    {ι : Type*} [Fintype ι] {f : ι → ℝ} {K A y : ℝ}
    (hy : y ≤ ∑ i : ι, f i) (hf : ∀ i, f i ≤ K * A) :
    y ≤ (Fintype.card ι : ℝ) * K * A := by
  classical
  calc
    y ≤ ∑ i : ι, f i := hy
    _ ≤ ∑ _i : ι, K * A := Finset.sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι : ℝ) * K * A := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact (mul_assoc _ _ _).symm

private theorem nonneg_array_entry_le_square_sum
    (K : ℕ → ℕ → ℝ) (hK : ∀ b c, 0 ≤ K b c) (s b c : ℕ) (hbc : b + c ≤ s) :
    K b c ≤ ∑ i : Fin (s + 1), ∑ j : Fin (s + 1), K i.val j.val := by
  classical
  let bi : Fin (s + 1) := ⟨b, by omega⟩
  let ci : Fin (s + 1) := ⟨c, by omega⟩
  have hc : K bi.val ci.val ≤ ∑ j : Fin (s + 1), K bi.val j.val :=
    Finset.single_le_sum (f := fun j : Fin (s + 1) => K bi.val j.val)
      (fun j _ => hK bi.val j.val) (Finset.mem_univ ci)
  have hb : (∑ j : Fin (s + 1), K bi.val j.val) ≤
      ∑ i : Fin (s + 1), ∑ j : Fin (s + 1), K i.val j.val :=
    Finset.single_le_sum (f := fun i : Fin (s + 1) =>
      ∑ j : Fin (s + 1), K i.val j.val)
      (fun i _ => Finset.sum_nonneg (fun j _ => hK i.val j.val))
      (Finset.mem_univ bi)
  have heq : K b c = K bi.val ci.val := rfl
  exact heq.trans_le (hc.trans hb)

private theorem cyclic_slot_sum_bound
    {V : Type*} (n : ℕ) (A : (Fin (n + 1) → V) → ℝ)
    (low P : V → ℝ) (Q : V → Prop) (K c : ℝ)
    (hrotate : ∀ w, A w = A (Fin.snoc (Fin.tail w) (w 0)))
    (hlast : ∀ (vs : Fin n → V), (∀ i, low (vs i) ≤ 1) →
      ∀ u, low u ≤ 1 → Q u →
        A (Fin.snoc vs u) ≤ K * (c + ∑ i : Fin n, P (vs i) + P u))
    (v : Fin (n + 1) → V) (hv : ∀ i, low (v i) ≤ 1)
    (i : Fin (n + 1)) (hi : Q (v i)) :
    A v ≤ K * (c + ∑ i : Fin (n + 1), P (v i)) := by
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → V) (j : Fin (n + 1)),
      j.val = k → Q (w j) → (∀ l, low (w l) ≤ 1) →
        A w ≤ K * (c + ∑ l : Fin (n + 1), P (w l)) := by
    intro k
    induction k with
    | zero =>
      intro w j hj hw hwlow
      have hj0 : j = 0 := Fin.ext hj
      have hw0 : Q (w 0) := Eq.mp (congrArg (fun a : Fin (n + 1) => Q (w a)) hj0) hw
      have hb := hlast (Fin.tail w) (fun l => hwlow l.succ) (w 0) (hwlow 0) hw0
      have hsum : (∑ l : Fin (n + 1), P (w l)) =
          P (w 0) + ∑ l : Fin n, P (Fin.tail w l) := Fin.sum_univ_succ _
      have heq : K * (c + ∑ l : Fin n, P (Fin.tail w l) + P (w 0)) =
          K * (c + ∑ l : Fin (n + 1), P (w l)) := by
        rw [hsum]
        ring
      exact (hrotate w).trans_le (hb.trans_eq heq)
    | succ k ih =>
      intro w j hj hw hwlow
      have hk : k < n := by have hjlt := j.isLt; omega
      let i' : Fin n := ⟨k, hk⟩
      let w' : Fin (n + 1) → V :=
        Fin.snoc (α := fun _ : Fin (n + 1) => V) (Fin.tail w) (w 0)
      have hij : i'.succ = j := Fin.ext hj.symm
      have hentry : w' i'.castSucc = w j :=
        (show w' i'.castSucc = w i'.succ from
          Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => V) (w 0) (Fin.tail w) i').trans
            (congrArg w hij)
      have hw' : Q (w' i'.castSucc) := Eq.mpr (congrArg Q hentry) hw
      have hwlow' (l : Fin (n + 1)) : low (w' l) ≤ 1 := by
        refine Fin.lastCases ?_ (fun a => ?_) l
        · simpa only [w', Fin.snoc_last] using hwlow 0
        · simpa only [w', Fin.snoc_castSucc, Fin.tail_def] using hwlow a.succ
      have hsum : (∑ l : Fin (n + 1), P (w' l)) =
          ∑ l : Fin (n + 1), P (w l) := by
        have hleft : (∑ l : Fin (n + 1), P (w' l)) =
            (∑ l : Fin n, P (Fin.tail w l)) + P (w 0) := by
          rw [Fin.sum_univ_castSucc]
          simp only [w', Fin.snoc_castSucc, Fin.snoc_last]
        have hright : (∑ l : Fin (n + 1), P (w l)) =
            P (w 0) + ∑ l : Fin n, P (Fin.tail w l) := Fin.sum_univ_succ _
        rw [hleft, hright, add_comm]
      exact (hrotate w).trans_le
        ((ih w' i'.castSucc rfl hw' hwlow').trans_eq
          (congrArg (fun r : ℝ => K * (c + r)) hsum))
  exact haux i.val v i rfl hi hv

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_state_weightedJetNorm_local_growth_all_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ b c : ℕ, b + c ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ,
      pairGrading (sectorGrading S) realGrading B v ≤ 1 → v.2 = 0 →
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (s + L) (vs i) +
          pairGrading (sectorGrading S) realGrading (s + L) v) := by
  classical
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  let interpolationData := hasInterpolation_localized_slot_growth_all p hp hI base loss 6
  let B : ℕ := interpolationData.choose
  let L : ℕ := interpolationData.choose_spec.choose
  have hB : base ≤ B := interpolationData.choose_spec.choose_spec.1
  refine ⟨B, L, hB, ?_⟩
  intro n R hR s hs
  let orderData := interpolationData.choose_spec.choose_spec.2 n R hR s hs
  let I : ℝ := orderData.choose
  have hI0 : 0 ≤ I := orderData.choose_spec.1
  let rawData (b c : ℕ) :=
    hN.endpointFlowScalarJets_state_weightedJetNorm_bound_uniform_radius hS hT n b c
  let K : ℕ → ℕ → ℝ := fun b c => (rawData b c).choose
  have hK (b c : ℕ) : 0 ≤ K b c := (rawData b c).choose_spec.1
  let K₀ : ℝ := ∑ b : Fin (s + 1), ∑ c : Fin (s + 1), K b.val c.val
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg (fun b _ =>
    Finset.sum_nonneg (fun c _ => hK b.val c.val))
  refine ⟨K₀ * I, mul_nonneg hK₀ hI0, ?_⟩
  intro rsel hrsel b c hbc z hz hzb vs hvs v hv hvq
  have hvs0 (i : Fin n) : p base (vs i) ≤ 1 :=
    (hp hB (vs i)).trans (hvs i)
  have hKs : K b c ≤ K₀ := nonneg_array_entry_le_square_sum K hK s b c hbc
  let Q : ℝ := (1 + p (b + loss) z + ∑ i : Fin n, p (b + loss) (vs i)) *
    p (base + c + 6) v + p (b + loss + c + 6) v
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact add_nonneg (mul_nonneg
      (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
        (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))) (apply_nonneg _ _))
      (apply_nonneg _ _)
  calc
    _ ≤ K b c * Q := (rawData b c).choose_spec.2 rsel hrsel z hz vs hvs0 v hvq
    _ ≤ K₀ * Q := mul_le_mul_of_nonneg_right hKs hQ
    _ ≤ K₀ * (I * (1 + p (s + L) z +
        ∑ i : Fin n, p (s + L) (vs i) + p (s + L) v)) :=
      mul_le_mul_of_nonneg_left (orderData.choose_spec.2 b c hbc z vs v hzb hvs hv) hK₀
    _ = _ := (mul_assoc K₀ I _).symm

theorem N01Properties.endpointFlowScalarJets_state_weightedJetNorm_local_growth_all
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ b c : ℕ, b + c ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ,
      pairGrading (sectorGrading S) realGrading B v ≤ 1 → v.2 = 0 →
      circleWeightedJetNorm T (3 / 4 : ℝ) b c
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (s + L) (vs i) +
          pairGrading (sectorGrading S) realGrading (s + L) v) := by
  let data := hN.endpointFlowScalarJets_state_weightedJetNorm_local_growth_all_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  exact ⟨orderData.choose, orderData.choose_spec.1, orderData.choose_spec.2 rsel hrsel⟩

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_state_circleNorm_local_growth_all_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ,
      pairGrading (sectorGrading S) realGrading B v ≤ 1 → v.2 = 0 →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (s + L) (vs i) +
          pairGrading (sectorGrading S) realGrading (s + L) v) := by
  classical
  let data := hN.endpointFlowScalarJets_state_weightedJetNorm_local_growth_all_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  let K : ℝ := orderData.choose
  have hK : 0 ≤ K := orderData.choose_spec.1
  refine ⟨(Fintype.card (CircleJetIndex s) : ℝ) * K,
    mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  intro rsel hrsel z hz hzb vs hvs v hv hvq
  let A : ℝ := 1 + pairGrading (sectorGrading S) realGrading (s + L) z +
    ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (s + L) (vs i) +
    pairGrading (sectorGrading S) realGrading (s + L) v
  exact finite_sum_bound_by_card (K := K) (A := A)
    (circleNorm_le_sum_weightedJetNorm
      (hN.endpointFlowScalarJets_state_circleMember hS hT rsel hrsel n z hz vs v hvq) s)
    (fun j => orderData.choose_spec.2 rsel hrsel _ _ j.property z hz hzb vs hvs v hv hvq)

theorem N01Properties.endpointFlowScalarJets_state_circleNorm_local_growth_all
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ vs : Fin n → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (vs i) ≤ 1) →
      ∀ v : StateDirections S × ℝ,
      pairGrading (sectorGrading S) realGrading B v ≤ 1 → v.2 = 0 →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (s + L) (vs i) +
          pairGrading (sectorGrading S) realGrading (s + L) v) := by
  let data := hN.endpointFlowScalarJets_state_circleNorm_local_growth_all_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  exact ⟨orderData.choose, orderData.choose_spec.1, orderData.choose_spec.2 rsel hrsel⟩

/-- The state slot may occur anywhere in the actual derivative tuple.
The right hand side is symmetric in all direction seminorms.
The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowScalarJets_state_slot_circleNorm_local_growth_all_uniform_radius
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (v i) ≤ 1) →
      (∃ i, (v i).2 = 0) →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin (n + 1), pairGrading (sectorGrading S) realGrading (s + L) (v i)) := by
  let data := hN.endpointFlowScalarJets_state_circleNorm_local_growth_all_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  let K : ℝ := orderData.choose
  have hK : 0 ≤ K := orderData.choose_spec.1
  refine ⟨K, hK, ?_⟩
  intro rsel hrsel z hz hzb v hv ⟨i, hi⟩
  let p := pairGrading (sectorGrading S) realGrading
  refine cyclic_slot_sum_bound n
    (fun w => circleNorm T (3 / 4 : ℝ) s
      (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w))
    (p B) (p (s + L)) (fun u : StateDirections S × ℝ => u.2 = 0)
    K (1 + p (s + L) z) ?_ ?_ v hv i hi
  · intro w
    exact congrArg (circleNorm T (3 / 4 : ℝ) s)
      (hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w)
  · intro vs hvs u hu huq
    exact orderData.choose_spec.2 rsel hrsel z hz hzb vs hvs u hu huq

theorem N01Properties.endpointFlowScalarJets_state_slot_circleNorm_local_growth_all
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ R →
      ∀ v : Fin (n + 1) → (StateDirections S × ℝ),
      (∀ i, pairGrading (sectorGrading S) realGrading B (v i) ≤ 1) →
      (∃ i, (v i).2 = 0) →
      circleNorm T (3 / 4 : ℝ) s
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z v) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) z +
          ∑ i : Fin (n + 1), pairGrading (sectorGrading S) realGrading (s + L) (v i)) := by
  let data := hN.endpointFlowScalarJets_state_slot_circleNorm_local_growth_all_uniform_radius hS hT
  let B : ℕ := data.choose
  let L : ℕ := data.choose_spec.choose
  have hB : base ≤ B := data.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  let orderData := data.choose_spec.choose_spec.2 n R hR s hs
  exact ⟨orderData.choose, orderData.choose_spec.1, orderData.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
