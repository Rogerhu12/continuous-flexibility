module

public import ContinuousFlexibility.Analysis.N04RealizationDoubleExpansionHeight

/-!
# The physical parameter budget in the two-coordinate expansion

A graph block with no original parameter slots has zero state component.
Consequently the existing double scalar expansion cannot use more outer
parameter derivatives than the sum of the original block counts.  The
identity below permits an exact truncation before applying the existing
height estimate; spatial differentiation does not enlarge that prefix.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A zero state component annihilates the parameter-head term. -/
theorem n04PulledFields_doubleExpansion_stateHead_zero
    (n : ℕ)
    (A : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (v : Fin (n + 1) → (E × ℝ) × ℝ) (hv : (v 0).1.1 = 0) :
    scalarAngularExpansion n
      (fun b j => scalarAngularExpansion j
        (fun a k => scalarAngularHead (fun a k => A a b k) (v 0).1 a k))
      (Fin.tail v) = 0 := by
  have hhead (b : ℕ) :
      (fun a k => scalarAngularHead (fun a k => A a b k) (v 0).1 a k) =
        (0 : ScalarAngularJetData E) := by
    funext a k
    apply MultilinearMap.ext
    intro u
    rw [scalarAngularHead_apply]
    exact (A a b (k + 1)).map_coord_zero 0
      (by simpa only [Fin.cons_zero] using hv)
  have hzero :
      (fun b j => scalarAngularExpansion j
        (fun a k => scalarAngularHead (fun a k => A a b k) (v 0).1 a k)) =
        (0 : ScalarAngularJetData (E × ℝ)) := by
    funext b j
    change scalarAngularExpansion j
      (fun a k => scalarAngularHead (fun a k => A a b k) (v 0).1 a k) =
        (0 : MultilinearMap ℝ (fun _ : Fin j => E × ℝ) ℝ)
    exact (congrArg (scalarAngularExpansion j) (hhead b)).trans
      (map_zero (scalarAngularExpansion j))
  rw [hzero, map_zero, zero_apply]

/-- Only the outer parameter prefix bounded by the original state count
can affect a graph-slot expansion. The spatial prefix remains its actual
total order, and neither scalar join is replaced by a different formula. -/
theorem n04PulledFields_doubleExpansion_congr_stateBudget
    (n : ℕ) (κ : Fin n → ℕ)
    (A B : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (hAB : ∀ a b j : ℕ, a + b + j ≤ n → j ≤ ∑ i, κ i →
      A a b j = B a b j)
    (v : Fin n → (E × ℝ) × ℝ)
    (hmask : ∀ i, κ i = 0 → (v i).1.1 = 0) :
    scalarAngularExpansion n
        (fun b j => scalarAngularExpansion j (fun a k => A a b k)) v =
      scalarAngularExpansion n
        (fun b j => scalarAngularExpansion j (fun a k => B a b k)) v := by
  induction n generalizing A B with
  | zero =>
      simp only [scalarAngularExpansion_zero_apply]
      exact congrArg (fun T => T Fin.elim0) (hAB 0 0 0 (by omega) (by simp))
  | succ n ih =>
      let AH : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => scalarAngularHead (fun a k => A a b k) (v 0).1 a j
      let BH : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => scalarAngularHead (fun a k => B a b k) (v 0).1 a j
      let AR : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => A (a + 1) b j
      let BR : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => B (a + 1) b j
      let AT : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => A a (b + 1) j
      let BT : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
        fun a b j => B a (b + 1) j
      have htail (j : ℕ) (hj : j ≤ ∑ i : Fin n, (Fin.tail κ) i) :
          j ≤ ∑ i, κ i := by
        rw [Fin.sum_univ_succ]
        exact hj.trans (Nat.le_add_left _ _)
      have hh : scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => AH a b k)) (Fin.tail v) =
        scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => BH a b k)) (Fin.tail v) := by
        by_cases hzero : κ 0 = 0
        · exact (n04PulledFields_doubleExpansion_stateHead_zero n A v (hmask 0 hzero)).trans
            (n04PulledFields_doubleExpansion_stateHead_zero n B v (hmask 0 hzero)).symm
        · apply ih (κ := Fin.tail κ) (A := AH) (B := BH)
            (v := Fin.tail v)
          · intro a b j hab hj
            apply MultilinearMap.ext
            intro u
            simp only [AH, BH, scalarAngularHead_apply]
            have hj' : j + 1 ≤ ∑ i, κ i := by
              rw [Fin.sum_univ_succ]
              change j ≤ ∑ i : Fin n, κ i.succ at hj
              omega
            exact congrArg (fun T => T (Fin.cons (v 0).1.1 u))
              (hAB a b (j + 1) (by omega) hj')
          · exact fun i hi => hmask i.succ hi
      have hr : scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => AR a b k)) (Fin.tail v) =
        scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => BR a b k)) (Fin.tail v) := by
        apply ih (κ := Fin.tail κ) (A := AR) (B := BR) (v := Fin.tail v)
        · intro a b j hab hj
          exact hAB (a + 1) b j (by omega) (htail j hj)
        · exact fun i hi => hmask i.succ hi
      have ha : scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => AT a b k)) (Fin.tail v) =
        scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => BT a b k)) (Fin.tail v) := by
        apply ih (κ := Fin.tail κ) (A := AT) (B := BT) (v := Fin.tail v)
        · intro a b j hab hj
          exact hAB a (b + 1) j (by omega) (htail j hj)
        · exact fun i hi => hmask i.succ hi
      rw [n04Realization_doubleAngularExpansion_succ_apply,
        n04Realization_doubleAngularExpansion_succ_apply]
      change scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => AH a b k)) (Fin.tail v) +
          (v 0).1.2 * scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => AR a b k)) (Fin.tail v) +
          (v 0).2 * scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => AT a b k)) (Fin.tail v) =
        scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => BH a b k)) (Fin.tail v) +
          (v 0).1.2 * scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => BR a b k)) (Fin.tail v) +
          (v 0).2 * scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j (fun a k => BT a b k)) (Fin.tail v)
      rw [hh, hr, ha]

/-- The original height estimate needs physical parameter orders only
through `K` when the graph's actual state counts sum to at most `K`. -/
theorem n04PulledFields_doubleExpansion_maskedHeight_bound
    (n r K : ℕ) (p : E → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (offset : ℕ) (κ β : Fin n → ℕ) (hpart : ∀ i, 0 < κ i + β i)
    (hbudget : (∑ i, κ i) ≤ K)
    (hA : ∀ a b j : ℕ, a + b + j ≤ n → j ≤ K → ∀ u : Fin j → E,
      |A a b j u| ≤ C * parameterHeightWeight H (r + j) *
        t ^ (a + b) * ∏ i, p (u i))
    (v : Fin n → (E × ℝ) × ℝ)
    (hmask : ∀ i, κ i = 0 → (v i).1.1 = 0)
    (hstate : ∀ i, p (v i).1.1 ≤ 2)
    (hrad : ∀ i, |(v i).1.2| ≤ M * parameterHeightWeight H (κ i) *
      t ^ (if κ i = 0 then β i - 1 else β i + offset))
    (hang : ∀ i, |(v i).2| ≤ M * parameterHeightWeight H (κ i) *
      t ^ (if κ i = 0 then β i - 1 else β i + offset)) :
    |scalarAngularExpansion n
        (fun b j => scalarAngularExpansion j (fun a k => A a b k)) v| ≤
      C * (4 * M * L) ^ n * parameterHeightWeight H (r + ∑ i, κ i) *
        t ^ (∑ i, (β i + (offset + 1) * κ i)) := by
  let B : ∀ a b j : ℕ, MultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
    fun a b j => if j ≤ K then A a b j else 0
  have heq := n04PulledFields_doubleExpansion_congr_stateBudget n κ A B
    (fun a b j _ hj => by simp only [B, if_pos (hj.trans hbudget)]) v hmask
  rw [heq]
  apply n04Realization_doubleAngularExpansion_height_bound n r p hp B
    hC hM hH hHL hL ht offset κ β hpart
  · intro a b j hab u
    by_cases hj : j ≤ K
    · simpa only [B, if_pos hj] using hA a b j hab hj u
    · simp only [B, if_neg hj, zero_apply, abs_zero]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hC (parameterHeightWeight_nonneg hH _))
          (pow_nonneg (zero_le_one.trans ht) _))
        (Finset.prod_nonneg (fun i _ => hp (u i)))
  · exact hstate
  · exact hrad
  · exact hang

end ContinuousFlexibility.Analysis
