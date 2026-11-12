import ContinuousFlexibility.Analysis.N01cStateAngleSelections

/-!
# Parameter-slot budgets for the original joint directions

The predicate records an existing state-angle word on the actual tuple.
Appending a pure spatial direction preserves its parameter budget.
Partition costs are summed with the exact arity identities of that word.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def N04RealizationMixedSlots (low high : Seminorm ℝ E)
    (K : ℕ) (R : ℝ) (n : ℕ) (v : Fin n → E × PolarPoint) : Prop :=
  ∃ w : StateAngleWord n, w.stateArity ≤ K ∧
    (∀ i, low (v i).1 ≤ 1) ∧ (∀ i, high (v i).1 ≤ R) ∧
    (∀ i, ‖(v i).2‖ ≤ 1) ∧
    (∀ i, w.isState i = false → (v i).1 = 0) ∧
    (∀ i, w.isState i = true → (v i).2 = 0)

theorem n04Realization_mixedSlots_parameters
    (low high : Seminorm ℝ E) {k K : ℕ} {R : ℝ} (hk : k ≤ K)
    (v : Fin k → E) (hlow : ∀ i, low (v i) ≤ 1) (hhigh : ∀ i, high (v i) ≤ R) :
    N04RealizationMixedSlots low high K R k (fun i => (v i, 0)) := by
  classical
  let w : StateAngleWord k := StateAngleWord.ofBool (fun _ => true)
  have hw : w.stateArity = k := by
    simp only [StateAngleWord.stateArity_eq_sum, w, StateAngleWord.isState_ofBool,
      ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine ⟨w, hw.trans_le hk, hlow, hhigh, ?_, ?_, ?_⟩
  · intro i
    simp only [norm_zero, zero_le_one]
  · intro i
    simp only [w, StateAngleWord.isState_ofBool, Bool.true_eq_false, false_implies]
  · intro i _
    rfl

theorem n04Realization_mixedSlots_snoc
    (low high : Seminorm ℝ E) {K n : ℕ} {R : ℝ} {v : Fin n → E × PolarPoint}
    (hR : 0 ≤ R) (hv : N04RealizationMixedSlots low high K R n v)
    (e : PolarPoint) (he : ‖e‖ ≤ 1) :
    N04RealizationMixedSlots low high K R (n + 1) (Fin.snoc v (0, e)) := by
  classical
  obtain ⟨w, hw, hl, hh, hp, hs, ha⟩ := hv
  let w' : StateAngleWord (n + 1) :=
    StateAngleWord.ofBool (Fin.snoc w.isState false)
  have hw' : w'.stateArity = w.stateArity := by
    rw [StateAngleWord.stateArity_eq_sum, Fin.sum_univ_castSucc]
    simp only [w', StateAngleWord.isState_ofBool, Fin.snoc_castSucc, Fin.snoc_last,
      Bool.false_eq_true, ite_false, add_zero, ← StateAngleWord.stateArity_eq_sum]
  refine ⟨w', hw'.trans_le hw, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, map_zero, zero_le_one]
    · simpa only [Fin.snoc_castSucc] using hl j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, map_zero] using hR
    · simpa only [Fin.snoc_castSucc] using hh j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using he
    · simpa only [Fin.snoc_castSucc] using hp j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro _
      simp only [Fin.snoc_last]
    · intro hj
      have hj' : w.isState j = false := by
        simpa only [w', StateAngleWord.isState_ofBool, Fin.snoc_castSucc] using hj
      simpa only [Fin.snoc_castSucc] using hs j hj'
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [w', StateAngleWord.isState_ofBool, Fin.snoc_last,
        Bool.false_eq_true, false_implies]
    · intro hj
      have hj' : w.isState j = true := by
        simpa only [w', StateAngleWord.isState_ofBool, Fin.snoc_castSucc] using hj
      simpa only [Fin.snoc_castSucc] using ha j hj'

theorem n04Realization_partition_mixedSlot_cost
    {n K s : ℕ} (w : StateAngleWord n) (c : OrderedFinpartition n) (offset : ℕ)
    (hn : n ≤ K + s) (hw : w.stateArity ≤ K) :
    (∑ i : Fin c.length, (w.restrict (c.emb i)).angleArity +
      (offset + 1) * (w.restrict (c.emb i)).stateArity) ≤ s + (offset + 1) * K := by
  calc
    _ = w.angleArity + (offset + 1) * w.stateArity := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        w.sum_restrict_angleArity c, w.sum_restrict_stateArity c]
    _ = (w.stateArity + w.angleArity) + offset * w.stateArity := by ring
    _ = n + offset * w.stateArity := by rw [w.arity_sum]
    _ ≤ K + s + offset * K := Nat.add_le_add hn (Nat.mul_le_mul_left offset hw)
    _ = s + (offset + 1) * K := by ring

end ContinuousFlexibility.Analysis
