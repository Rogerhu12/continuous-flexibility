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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

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
  classical
  let p := pairGrading (sectorGrading S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone S
  have hI : HasInterpolation p := hasInterpolation_of_hasSmoothing hp
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
  obtain ⟨B, L, hB, hinterp⟩ :=
    hasInterpolation_localized_slot_growth_all p hp hI base loss 6
  refine ⟨B, L, hB, ?_⟩
  intro n R hR s hs
  obtain ⟨I, hI0, hi⟩ := hinterp n R hR s hs
  have hraw (b c : ℕ) :=
    hN.endpointFlowScalarJets_state_weightedJetNorm_bound hS hT rsel hrsel n b c
  choose K hK hk using hraw
  let K₀ : ℝ := ∑ b : Fin (s + 1), ∑ c : Fin (s + 1), K b.val c.val
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg (fun b _ =>
    Finset.sum_nonneg (fun c _ => hK b.val c.val))
  refine ⟨K₀ * I, mul_nonneg hK₀ hI0, ?_⟩
  intro b c hbc z hz hzb vs hvs v hv hvq
  have hvs0 (i : Fin n) : p base (vs i) ≤ 1 :=
    (hp hB (vs i)).trans (hvs i)
  have hKs : K b c ≤ K₀ := by
    let bi : Fin (s + 1) := ⟨b, by omega⟩
    let ci : Fin (s + 1) := ⟨c, by omega⟩
    have hc : K b c ≤ ∑ j : Fin (s + 1), K bi.val j.val :=
      Finset.single_le_sum (f := fun j : Fin (s + 1) => K bi.val j.val)
        (fun j _ => hK bi.val j.val) (Finset.mem_univ ci)
    have hb : (∑ j : Fin (s + 1), K bi.val j.val) ≤ K₀ :=
      Finset.single_le_sum (f := fun i : Fin (s + 1) =>
        ∑ j : Fin (s + 1), K i.val j.val)
        (fun i _ => Finset.sum_nonneg (fun j _ => hK i.val j.val))
        (Finset.mem_univ bi)
    exact hc.trans hb
  let Q : ℝ := (1 + p (b + loss) z + ∑ i : Fin n, p (b + loss) (vs i)) *
    p (base + c + 6) v + p (b + loss + c + 6) v
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact add_nonneg (mul_nonneg
      (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _))
        (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))) (apply_nonneg _ _))
      (apply_nonneg _ _)
  calc
    _ ≤ K b c * Q := hk b c z hz vs hvs0 v hvq
    _ ≤ K₀ * Q := mul_le_mul_of_nonneg_right hKs hQ
    _ ≤ K₀ * (I * (1 + p (s + L) z +
        ∑ i : Fin n, p (s + L) (vs i) + p (s + L) v)) :=
      mul_le_mul_of_nonneg_left (hi b c hbc z vs v hzb hvs hv) hK₀
    _ = _ := by dsimp only [p]; ring

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
  classical
  obtain ⟨B, L, hB, hbound⟩ :=
    hN.endpointFlowScalarJets_state_weightedJetNorm_local_growth_all hS hT rsel hrsel
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  obtain ⟨K, hK, hk⟩ := hbound n R hR s hs
  refine ⟨(Fintype.card (CircleJetIndex s) : ℝ) * K,
    mul_nonneg (Nat.cast_nonneg _) hK, ?_⟩
  intro z hz hzb vs hvs v hv hvq
  let A : ℝ := 1 + pairGrading (sectorGrading S) realGrading (s + L) z +
    ∑ i : Fin n, pairGrading (sectorGrading S) realGrading (s + L) (vs i) +
    pairGrading (sectorGrading S) realGrading (s + L) v
  calc
    _ ≤ ∑ j : CircleJetIndex s, circleWeightedJetNorm T (3 / 4 : ℝ)
        (j.val 0).val (j.val 1).val
        (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z (Fin.snoc vs v)) :=
      circleNorm_le_sum_weightedJetNorm
        (hN.endpointFlowScalarJets_state_circleMember hS hT rsel hrsel n z hz vs v hvq) s
    _ ≤ ∑ _j : CircleJetIndex s, K * A := by
      apply Finset.sum_le_sum
      intro j _
      exact hk _ _ j.property z hz hzb vs hvs v hv hvq
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [A]
      ring

/-- The state slot may occur anywhere in the actual derivative tuple.
The right hand side is symmetric in all direction seminorms. -/
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
  obtain ⟨B, L, hB, hbound⟩ :=
    hN.endpointFlowScalarJets_state_circleNorm_local_growth_all hS hT rsel hrsel
  refine ⟨B, L, hB, fun n R hR s hs => ?_⟩
  obtain ⟨K, hK, hk⟩ := hbound n R hR s hs
  refine ⟨K, hK, ?_⟩
  intro z hz hzb v hv ⟨i, hi⟩
  let p := pairGrading (sectorGrading S) realGrading
  have haux : ∀ k : ℕ, ∀ (w : Fin (n + 1) → (StateDirections S × ℝ))
      (j : Fin (n + 1)), j.val = k → (w j).2 = 0 →
      (∀ l, p B (w l) ≤ 1) →
      circleNorm T (3 / 4 : ℝ) s (hN.endpointFlowScalarJets hS hT rsel hrsel (n + 1) z w) ≤
        K * (1 + p (s + L) z + ∑ l : Fin (n + 1), p (s + L) (w l)) := by
    intro k
    induction k with
    | zero =>
      intro w j hj hw hwlow
      have hj0 : j = 0 := Fin.ext hj
      rw [hj0] at hw
      rw [hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w]
      have hb := hk z hz hzb (Fin.tail w) (fun l => hwlow l.succ)
        (w 0) (hwlow 0) hw
      have hsum : (∑ l : Fin (n + 1), p (s + L) (w l)) =
          p (s + L) (w 0) + ∑ l : Fin n, p (s + L) (Fin.tail w l) :=
        Fin.sum_univ_succ _
      apply hb.trans_eq
      rw [hsum]
      dsimp only [p]
      ring
    | succ k ih =>
      intro w j hj hw hwlow
      have hklt : k < n := by have hjlt := j.isLt; omega
      let i' : Fin n := ⟨k, hklt⟩
      let w' : Fin (n + 1) → (StateDirections S × ℝ) :=
        Fin.snoc (Fin.tail w) (w 0)
      have hij : i'.succ = j := Fin.ext (by simpa only [i', Fin.val_succ] using hj.symm)
      have hw' : (w' i'.castSucc).2 = 0 := by
        dsimp only [w']
        rw [Fin.snoc_castSucc]
        change (w i'.succ).2 = 0
        rw [hij]
        exact hw
      have hwlow' (l : Fin (n + 1)) : p B (w' l) ≤ 1 := by
        refine Fin.lastCases ?_ (fun a => ?_) l
        · simpa only [w', Fin.snoc_last] using hwlow 0
        · simpa only [w', Fin.snoc_castSucc] using hwlow a.succ
      have hsum : (∑ l : Fin (n + 1), p (s + L) (w' l)) =
          ∑ l : Fin (n + 1), p (s + L) (w l) := by
        have hleft : (∑ l : Fin (n + 1), p (s + L) (w' l)) =
            (∑ l : Fin n, p (s + L) (Fin.tail w l)) + p (s + L) (w 0) := by
          rw [Fin.sum_univ_castSucc]
          simp only [w', Fin.snoc_castSucc, Fin.snoc_last]
        have hright : (∑ l : Fin (n + 1), p (s + L) (w l)) =
            p (s + L) (w 0) + ∑ l : Fin n, p (s + L) (Fin.tail w l) :=
          Fin.sum_univ_succ _
        rw [hleft, hright, add_comm]
      rw [hN.endpointFlowScalarJets_rotate hS hT rsel hrsel n z hz w]
      have hb := ih w' i'.castSucc rfl hw' hwlow'
      simpa only [hsum] using hb
  exact haux i.val v i rfl hi hv

end ContinuousFlexibility.Statements
