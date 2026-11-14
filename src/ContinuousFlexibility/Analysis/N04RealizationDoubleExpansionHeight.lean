module

public import ContinuousFlexibility.Analysis.N04RealizationJointExpansionBounds
public import ContinuousFlexibility.Analysis.N04RealizationMovingGraphBounds
public import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget

/-!
# Height factors in the existing two-coordinate expansion

The actual scalar expansion is applied twice, in radial-then-angular
order. Its successor has one parameter term and two spatial terms.
The finite estimate retains the height factor at positive parameter
order and allows an unweighted value at parameter order zero.

The outer mixed prefix may use the total order. For the physical
coefficient application its all-order loss is fixed, so this changes
only the permitted finite-prefix constant. The inverse block orders
are still the counts of the original parameter slots.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Expand the two existing scalar joins, without introducing a new
representation for their multilinear maps. -/
theorem n04Realization_doubleAngularExpansion_succ_apply
    (n : ℕ)
    (A : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (v : Fin (n + 1) → (E × ℝ) × ℝ) :
    scalarAngularExpansion (n + 1)
        (fun b k => scalarAngularExpansion k (fun a j => A a b j)) v =
      scalarAngularExpansion n
        (fun b k => scalarAngularExpansion k
          (fun a j => scalarAngularHead (fun a j => A a b j) (v 0).1 a j))
        (Fin.tail v) +
      (v 0).1.2 * scalarAngularExpansion n
        (fun b k => scalarAngularExpansion k
          (fun a j => scalarAngularShift (fun a j => A a b j) a j))
        (Fin.tail v) +
      (v 0).2 * scalarAngularExpansion n
        (fun b k => scalarAngularExpansion k (fun a j => A a (b + 1) j))
        (Fin.tail v) := by
  let B : ScalarAngularJetData (E × ℝ) :=
    fun b k => scalarAngularExpansion k (fun a j => A a b j)
  let AH : ScalarAngularJetData (E × ℝ) :=
    fun b k => scalarAngularExpansion k
      (fun a j => scalarAngularHead (fun a j => A a b j) (v 0).1 a j)
  let AR : ScalarAngularJetData (E × ℝ) :=
    fun b k => scalarAngularExpansion k
      (fun a j => scalarAngularShift (fun a j => A a b j) a j)
  let AT : ScalarAngularJetData (E × ℝ) :=
    fun b k => scalarAngularExpansion k (fun a j => A a (b + 1) j)
  have hhead : scalarAngularHead B (v 0) = AH + (v 0).1.2 • AR := by
    funext b k
    apply MultilinearMap.ext
    intro u
    simp only [scalarAngularHead_apply, B, AH, AR, Pi.add_apply,
      Pi.smul_apply, MultilinearMap.add_apply, MultilinearMap.smul_apply, smul_eq_mul]
    rw [scalarAngularExpansion_succ_apply]
    simp only [Fin.cons_zero, Fin.tail_cons]
  have hshift : scalarAngularShift B = AT := rfl
  change scalarAngularExpansion (n + 1) B v =
    scalarAngularExpansion n AH (Fin.tail v) +
      (v 0).1.2 * scalarAngularExpansion n AR (Fin.tail v) +
      (v 0).2 * scalarAngularExpansion n AT (Fin.tail v)
  rw [scalarAngularExpansion_succ_apply, hhead, hshift,
    (scalarAngularExpansion n).map_add, (scalarAngularExpansion n).map_smul]
  simp only [MultilinearMap.add_apply, MultilinearMap.smul_apply, smul_eq_mul]

/-- A parameter head supplies a height factor even when its graph block
had no parameter slots. In that case the uniform height bound suffices. -/
theorem n04Realization_parameterHeightWeight_head_le
    {H L : ℝ} (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    (r κ q : ℕ) :
    parameterHeightWeight H (r + 1 + q) ≤
      L * parameterHeightWeight H (r + κ + q) := by
  have hpos : r + 1 + q ≠ 0 := by omega
  by_cases hzero : r + κ + q = 0
  · simpa only [parameterHeightWeight, if_neg hpos, if_pos hzero, mul_one] using hHL
  · simp only [parameterHeightWeight, if_neg hpos, if_neg hzero]
    nlinarith

/-- Each graph slot has its original parameter and spatial counts.
The outer constant occurs once, and the surviving height exponent is
determined by the original parameter count, including its zero case. -/
theorem n04Realization_doubleAngularExpansion_height_bound
    (n r : ℕ) (p : E → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (offset : ℕ) (κ β : Fin n → ℕ) (hpart : ∀ i, 0 < κ i + β i)
    (hA : ∀ a b k : ℕ, a + b + k ≤ n → ∀ u : Fin k → E,
      |A a b k u| ≤ C * parameterHeightWeight H (r + k) *
        t ^ (a + b) * ∏ i, p (u i))
    (v : Fin n → (E × ℝ) × ℝ)
    (hstate : ∀ i, p (v i).1.1 ≤ 2)
    (hrad : ∀ i, |(v i).1.2| ≤ M * parameterHeightWeight H (κ i) *
      t ^ (if κ i = 0 then β i - 1 else β i + offset))
    (hang : ∀ i, |(v i).2| ≤ M * parameterHeightWeight H (κ i) *
      t ^ (if κ i = 0 then β i - 1 else β i + offset)) :
    |scalarAngularExpansion n
        (fun b k => scalarAngularExpansion k (fun a j => A a b j)) v| ≤
      C * (4 * M * L) ^ n * parameterHeightWeight H (r + ∑ i, κ i) *
        t ^ (∑ i, (β i + (offset + 1) * κ i)) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  induction n generalizing A C r with
  | zero =>
      simpa only [scalarAngularExpansion_zero_apply, pow_zero,
        Fin.sum_univ_zero, Fin.prod_univ_zero, Nat.add_zero, mul_one] using
        hA 0 0 0 (by omega) Fin.elim0
  | succ n ih =>
      let AH : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
        fun a b k => scalarAngularHead (fun a j => A a b j) (v 0).1 a k
      let AR : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
        fun a b k => scalarAngularShift (fun a j => A a b j) a k
      let AT : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
        fun a b k => A a (b + 1) k
      have hAH (a b k : ℕ) (hab : a + b + k ≤ n) (u : Fin k → E) :
          |AH a b k u| ≤ (C * p (v 0).1.1) *
            parameterHeightWeight H ((r + 1) + k) * t ^ (a + b) * ∏ i, p (u i) := by
        have h := hA a b (k + 1) (by omega) (Fin.cons (v 0).1.1 u)
        simpa only [AH, scalarAngularHead_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          mul_assoc, mul_comm, mul_left_comm] using h
      have hAR (a b k : ℕ) (hab : a + b + k ≤ n) (u : Fin k → E) :
          |AR a b k u| ≤ (C * t) * parameterHeightWeight H (r + k) *
            t ^ (a + b) * ∏ i, p (u i) := by
        have h := hA (a + 1) b k (by omega) u
        have he : (a + 1) + b = (a + b) + 1 := by omega
        simpa only [AR, scalarAngularShift_apply, he, pow_succ,
          mul_assoc, mul_comm, mul_left_comm] using h
      have hAT (a b k : ℕ) (hab : a + b + k ≤ n) (u : Fin k → E) :
          |AT a b k u| ≤ (C * t) * parameterHeightWeight H (r + k) *
            t ^ (a + b) * ∏ i, p (u i) := by
        have h := hA a (b + 1) k (by omega) u
        have he : a + (b + 1) = (a + b) + 1 := by omega
        simpa only [AT, he, pow_succ,
          mul_assoc, mul_comm, mul_left_comm] using h
      have hh := ih (r := r + 1) (A := AH) (C := C * p (v 0).1.1)
        (hC := mul_nonneg hC (hp _))
        (κ := Fin.tail κ) (β := Fin.tail β) (hpart := fun i => hpart i.succ)
        (hA := hAH) (v := Fin.tail v) (hstate := fun i => hstate i.succ)
        (hrad := fun i => hrad i.succ) (hang := fun i => hang i.succ)
      have hr := ih (r := r) (A := AR) (C := C * t)
        (hC := mul_nonneg hC ht0)
        (κ := Fin.tail κ) (β := Fin.tail β) (hpart := fun i => hpart i.succ)
        (hA := hAR) (v := Fin.tail v) (hstate := fun i => hstate i.succ)
        (hrad := fun i => hrad i.succ) (hang := fun i => hang i.succ)
      have ha := ih (r := r) (A := AT) (C := C * t)
        (hC := mul_nonneg hC ht0)
        (κ := Fin.tail κ) (β := Fin.tail β) (hpart := fun i => hpart i.succ)
        (hA := hAT) (v := Fin.tail v) (hstate := fun i => hstate i.succ)
        (hrad := fun i => hrad i.succ) (hang := fun i => hang i.succ)
      let W : ℝ := 4 * M * L
      let q : ℕ := ∑ i : Fin n, κ i.succ
      let d : ℕ := β 0 + (offset + 1) * κ 0
      let e : ℕ := if κ 0 = 0 then β 0 - 1 else β 0 + offset
      let D : ℕ := ∑ i : Fin n, (β i.succ + (offset + 1) * κ i.succ)
      let P : ℝ := parameterHeightWeight H (r + κ 0 + q)
      let Z : ℝ := C * W ^ n * P * t ^ (d + D)
      have hW0 : 0 ≤ W := mul_nonneg (mul_nonneg (by norm_num) hM0) hL0
      have hP0 : 0 ≤ P := parameterHeightWeight_nonneg hH _
      have hκ0 : 0 ≤ parameterHeightWeight H (κ 0) := parameterHeightWeight_nonneg hH _
      have hq0 : 0 ≤ parameterHeightWeight H (r + q) := parameterHeightWeight_nonneg hH _
      have hhead0 : 0 ≤ parameterHeightWeight H (r + 1 + q) :=
        parameterHeightWeight_nonneg hH _
      have hZ0 : 0 ≤ Z := by
        exact mul_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg hW0 _)) hP0)
          (pow_nonneg ht0 _)
      have hheadHeight : parameterHeightWeight H (r + 1 + q) ≤ L * P :=
        n04Realization_parameterHeightWeight_head_le hH hHL hL r (κ 0) q
      have hmerge : parameterHeightWeight H (κ 0) *
          parameterHeightWeight H (r + q) ≤ L * P := by
        simpa only [P, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          n01c_parameterHeightWeight_mul_le hH hHL hL (κ 0) (r + q)
      have hpow : t ^ (e + 1 + D) ≤ t ^ (d + D) :=
        pow_le_pow_right₀ ht (Nat.add_le_add_right
          (n04Realization_movingGraph_block_order (κ 0) (β 0) offset (hpart 0)) D)
      have htailpow : t ^ D ≤ t ^ (d + D) :=
        pow_le_pow_right₀ ht (Nat.le_add_left D d)
      have hheadBound :
          |scalarAngularExpansion n
            (fun b k => scalarAngularExpansion k (fun a j => AH a b j)) (Fin.tail v)| ≤
            (2 * L) * Z := by
        calc
          _ ≤ (C * p (v 0).1.1) * W ^ n *
              parameterHeightWeight H (r + 1 + q) * t ^ D := hh
          _ ≤ (C * 2) * W ^ n * (L * P) * t ^ (d + D) := by
            gcongr <;> first | exact hstate 0 | exact hheadHeight | exact htailpow
          _ = _ := by dsimp only [Z]; ring
      have hspatialBound
          (c : ℝ)
          (X : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
          (hc : |c| ≤ M * parameterHeightWeight H (κ 0) * t ^ e)
          (hx : |scalarAngularExpansion n
            (fun b k => scalarAngularExpansion k (fun a j => X a b j)) (Fin.tail v)| ≤
              (C * t) * W ^ n * parameterHeightWeight H (r + q) * t ^ D) :
          |c| * |scalarAngularExpansion n
            (fun b k => scalarAngularExpansion k (fun a j => X a b j)) (Fin.tail v)| ≤
              (M * L) * Z := by
        calc
          _ ≤ (M * parameterHeightWeight H (κ 0) * t ^ e) *
              ((C * t) * W ^ n * parameterHeightWeight H (r + q) * t ^ D) :=
            mul_le_mul hc hx (abs_nonneg _) (by positivity)
          _ = (C * M) * W ^ n *
              (parameterHeightWeight H (κ 0) * parameterHeightWeight H (r + q)) *
              t ^ (e + 1 + D) := by
            rw [pow_add, pow_succ]
            ring
          _ ≤ (C * M) * W ^ n * (L * P) * t ^ (d + D) := by
            gcongr <;> assumption
          _ = _ := by dsimp only [Z]; ring
      have hr' := hspatialBound (v 0).1.2 AR (hrad 0) hr
      have ha' := hspatialBound (v 0).2 AT (hang 0) ha
      rw [n04Realization_doubleAngularExpansion_succ_apply]
      calc
        _ ≤ |scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AH a b j)) (Fin.tail v)| +
            |(v 0).1.2| * |scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AR a b j)) (Fin.tail v)| +
            |(v 0).2| * |scalarAngularExpansion n
              (fun b k => scalarAngularExpansion k (fun a j => AT a b j)) (Fin.tail v)| := by
          refine (abs_add_le _ _).trans ?_
          calc
            _ ≤ |scalarAngularExpansion n
                  (fun b k => scalarAngularExpansion k (fun a j => AH a b j)) (Fin.tail v)| +
                |(v 0).1.2 * scalarAngularExpansion n
                  (fun b k => scalarAngularExpansion k (fun a j => AR a b j)) (Fin.tail v)| +
                |(v 0).2 * scalarAngularExpansion n
                  (fun b k => scalarAngularExpansion k (fun a j => AT a b j)) (Fin.tail v)| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ (2 * L) * Z + (M * L) * Z + (M * L) * Z :=
          add_le_add (add_le_add hheadBound hr') ha'
        _ = (2 * L + 2 * M * L) * Z := by ring
        _ ≤ (4 * M * L) * Z :=
          mul_le_mul_of_nonneg_right (by nlinarith) hZ0
        _ = _ := by
          simp only [Z, W, P, q, d, D, Fin.sum_univ_succ, pow_succ,
            Nat.add_assoc]
          ring

end ContinuousFlexibility.Analysis
