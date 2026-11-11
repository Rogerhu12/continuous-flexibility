import ContinuousFlexibility.Analysis.N01cStateAngleSelections
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# The distributed order budget of a state-flow graph term

The outer word selects either the identity state coordinate or an actual
flow factor from each partition block. Zero-state flow factors cost one
less angular order. Positive-state flow factors carry their fixed prefix
offset. The resulting budget depends on the number of state slots, not
on the number of angular slots.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped BigOperators

namespace StateAngleWord

def selectedSum : {n : ℕ} → StateAngleWord n → (Fin n → ℕ) → ℕ
  | _, .nil, _ => 0
  | _, .state w, f => w.selectedSum (Fin.tail f)
  | _, .angle w, f => f 0 + w.selectedSum (Fin.tail f)

def selectedProduct : {n : ℕ} → StateAngleWord n → (Fin n → ℝ) → ℝ
  | _, .nil, _ => 1
  | _, .state w, f => w.selectedProduct (Fin.tail f)
  | _, .angle w, f => f 0 * w.selectedProduct (Fin.tail f)

theorem angleFactor_eq_selectedProduct {E : Type*} {n : ℕ}
    (w : StateAngleWord n) (v : Fin n → E × ℝ) :
    w.angleFactor v = w.selectedProduct (fun i => (v i).2) := by
  induction w with
  | nil => rfl
  | state w ih => exact ih (Fin.tail v)
  | angle w ih =>
      change (v 0).2 * w.angleFactor (Fin.tail v) = _
      rw [ih]
      rfl

theorem selectedProduct_nonneg {n : ℕ} (w : StateAngleWord n)
    {f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ w.selectedProduct f := by
  induction w with
  | nil => exact zero_le_one
  | state w ih => exact ih (fun i => hf i.succ)
  | angle w ih => exact mul_nonneg (hf 0) (ih (fun i => hf i.succ))

theorem selectedProduct_mono {n : ℕ} (w : StateAngleWord n)
    {f g : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    w.selectedProduct f ≤ w.selectedProduct g := by
  induction w with
  | nil => exact le_rfl
  | state w ih => exact ih (fun i => hf i.succ) (fun i => hfg i.succ)
  | angle w ih =>
      exact mul_le_mul (hfg 0) (ih (fun i => hf i.succ) (fun i => hfg i.succ))
        (w.selectedProduct_nonneg (fun i => hf i.succ)) ((hf 0).trans (hfg 0))

theorem selectedProduct_mul {n : ℕ} (w : StateAngleWord n)
    (f g : Fin n → ℝ) :
    w.selectedProduct (fun i => f i * g i) =
      w.selectedProduct f * w.selectedProduct g := by
  induction w with
  | nil => simp only [selectedProduct, one_mul]
  | state w ih => exact ih (Fin.tail f) (Fin.tail g)
  | angle w ih =>
      simp only [selectedProduct, Fin.tail_def, ih]
      ring

theorem selectedProduct_const {n : ℕ} (w : StateAngleWord n) (c : ℝ) :
    w.selectedProduct (fun _ => c) = c ^ w.angleArity := by
  induction w with
  | nil => simp only [selectedProduct, angleArity, pow_zero]
  | state w ih => exact ih
  | angle w ih =>
      simp only [selectedProduct, Fin.tail_def, angleArity, ih, pow_succ]
      ring

theorem abs_angleFactor {E : Type*} {n : ℕ} (w : StateAngleWord n)
    (v : Fin n → E × ℝ) :
    |w.angleFactor v| = w.selectedProduct (fun i => |(v i).2|) := by
  induction w with
  | nil => simp only [angleFactor, selectedProduct, abs_one]
  | state w ih => exact ih (Fin.tail v)
  | angle w ih =>
      simp only [angleFactor, selectedProduct, Fin.tail_def, abs_mul, ih]

theorem selectedProduct_spatialPower {n : ℕ} (w : StateAngleWord n)
    (orders : Fin n → ℕ) {R : ℝ} (hR : 0 < R) (s : ℕ) :
    w.selectedProduct (fun i => R ^ ((orders i : ℝ) / ((s : ℝ) + 1))) =
      R ^ (((w.selectedSum orders : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  induction w with
  | nil =>
      simp only [selectedProduct, selectedSum, Nat.cast_zero, zero_div, Real.rpow_zero]
  | state w ih => exact ih (Fin.tail orders)
  | angle w ih =>
      simp only [selectedProduct, selectedSum, Fin.tail_def, ih]
      exact rpow_spatialOrder_mul hR (orders 0) (w.selectedSum (Fin.tail orders)) s

/-- Effective spatial order of all selected flow factors together with
the outer function's angle derivatives. -/
def flowSpatialOrder {n : ℕ} (w : StateAngleWord n)
    (κ β : Fin n → ℕ) (offset : ℕ) : ℕ :=
  w.angleArity + w.selectedSum (fun i => if κ i = 0 then β i - 1 else β i + offset)

/-- Any selected state coordinate already differentiates the outer
function in a positive state order. -/
def flowParameterOrder {n : ℕ} (w : StateAngleWord n) (κ : Fin n → ℕ) : ℕ :=
  w.stateArity + w.selectedSum κ

theorem flowSpatialOrder_le {n : ℕ} (w : StateAngleWord n)
    (κ β : Fin n → ℕ) (offset : ℕ) (hpart : ∀ i, 0 < κ i + β i) :
    w.flowSpatialOrder κ β offset ≤
      (∑ i, β i) + (offset + 1) * ∑ i, κ i := by
  induction w with
  | nil =>
      simp only [flowSpatialOrder, angleArity, selectedSum, Fin.sum_univ_zero,
        Nat.mul_zero, Nat.add_zero, le_refl]
  | state w ih =>
      have ht := ih (Fin.tail κ) (Fin.tail β) (fun i => hpart i.succ)
      change w.flowSpatialOrder (Fin.tail κ) (Fin.tail β) offset ≤ _
      apply ht.trans
      simp only [Fin.sum_univ_succ, Fin.tail_def, Nat.mul_add]
      omega
  | angle w ih =>
      have ht := ih (Fin.tail κ) (Fin.tail β) (fun i => hpart i.succ)
      have hhead := hpart 0
      have hheadOrder : 1 + (if κ 0 = 0 then β 0 - 1 else β 0 + offset) ≤
          β 0 + (offset + 1) * κ 0 := by
        by_cases hk : κ 0 = 0
        · simp only [hk, if_pos rfl, ite_true, Nat.mul_zero, Nat.add_zero]
          omega
        · have hmul : offset + 1 ≤ (offset + 1) * κ 0 := by
            simpa only [Nat.mul_one] using
              Nat.mul_le_mul_left (offset + 1) (show 1 ≤ κ 0 by omega)
          simp only [if_neg hk]
          omega
      calc
        _ = (1 + (if κ 0 = 0 then β 0 - 1 else β 0 + offset)) +
            w.flowSpatialOrder (Fin.tail κ) (Fin.tail β) offset := by
          simp only [flowSpatialOrder, angleArity, selectedSum, Fin.tail_def]
          ac_rfl
        _ ≤ (β 0 + (offset + 1) * κ 0) +
            ((∑ i, (Fin.tail β) i) + (offset + 1) * ∑ i, (Fin.tail κ) i) :=
          Nat.add_le_add hheadOrder ht
        _ = _ := by
          simp only [Fin.sum_univ_succ, Fin.tail_def, Nat.mul_add]
          ac_rfl

theorem flowParameterOrder_pos {n : ℕ} (w : StateAngleWord n)
    (κ : Fin n → ℕ) (hk : 0 < ∑ i, κ i) : 0 < w.flowParameterOrder κ := by
  induction w with
  | nil =>
      simpa only [Fin.sum_univ_zero, flowParameterOrder, stateArity,
        selectedSum, Nat.zero_add] using hk
  | state w ih =>
      simp only [flowParameterOrder, stateArity, selectedSum]
      omega
  | angle w ih =>
      by_cases hzero : κ 0 = 0
      · have ht : 0 < ∑ i, (Fin.tail κ) i := by
          simpa only [Fin.sum_univ_succ, hzero, Nat.zero_add, Fin.tail_def] using hk
        have hh := ih (Fin.tail κ) ht
        simpa only [flowParameterOrder, stateArity, selectedSum, hzero, Nat.zero_add] using hh
      · simp only [flowParameterOrder, stateArity, selectedSum]
        omega

/-- The original partition's state and angle counts give the final
budget, even for terms whose identity-coordinate factor vanishes. -/
theorem partition_flowSpatialOrder_le {n : ℕ} (input : StateAngleWord n)
    (c : _root_.OrderedFinpartition n) (output : StateAngleWord c.length) (offset : ℕ) :
    output.flowSpatialOrder
        (fun i => (input.restrict (c.emb i)).stateArity)
        (fun i => (input.restrict (c.emb i)).angleArity) offset ≤
      input.angleArity + (offset + 1) * input.stateArity := by
  have hh := output.flowSpatialOrder_le
    (fun i => (input.restrict (c.emb i)).stateArity)
    (fun i => (input.restrict (c.emb i)).angleArity) offset
    (fun i => by rw [(input.restrict (c.emb i)).arity_sum]; exact c.partSize_pos i)
  simpa only [input.sum_restrict_angleArity c, input.sum_restrict_stateArity c] using hh

theorem partition_flowParameterOrder_pos {n : ℕ} (input : StateAngleWord n)
    (c : _root_.OrderedFinpartition n) (output : StateAngleWord c.length)
    (hk : 0 < input.stateArity) :
    0 < output.flowParameterOrder (fun i => (input.restrict (c.emb i)).stateArity) := by
  apply output.flowParameterOrder_pos
  simpa only [input.sum_restrict_stateArity c] using hk

end StateAngleWord

/-- Multiplying height factors keeps a single genuine height factor as
soon as one of the parameter orders is positive. -/
theorem n01c_parameterHeightWeight_mul_le {H L : ℝ}
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (j k : ℕ) :
    parameterHeightWeight H j * parameterHeightWeight H k ≤
      L * parameterHeightWeight H (j + k) := by
  by_cases hj : j = 0 <;> by_cases hk : k = 0
  · simp only [hj, hk, Nat.zero_add, parameterHeightWeight, if_pos rfl, ite_true, one_mul, mul_one]
    exact hL
  · have hsum : j + k ≠ 0 := by omega
    simp only [parameterHeightWeight, if_pos hj, if_neg hk, if_neg hsum, one_mul]
    nlinarith
  · have hsum : j + k ≠ 0 := by omega
    simp only [parameterHeightWeight, if_neg hj, if_pos hk, if_neg hsum, mul_one]
    nlinarith
  · have hsum : j + k ≠ 0 := by omega
    simp only [parameterHeightWeight, if_neg hj, if_neg hk, if_neg hsum]
    exact mul_le_mul_of_nonneg_right hHL hH

theorem StateAngleWord.selected_heightProduct_le
    {n : ℕ} (w : StateAngleWord n) (κ : Fin n → ℕ) {H L : ℝ}
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (j : ℕ) :
    parameterHeightWeight H (j + w.stateArity) *
        w.selectedProduct (fun i => parameterHeightWeight H (κ i)) ≤
      L ^ n * parameterHeightWeight H (j + w.flowParameterOrder κ) := by
  induction w generalizing j with
  | nil =>
      simp only [StateAngleWord.stateArity, StateAngleWord.selectedProduct,
        StateAngleWord.flowParameterOrder, StateAngleWord.selectedSum, Nat.add_zero,
        pow_zero, one_mul, mul_one, le_refl]
  | @state n w ih =>
      have hh := ih (κ := Fin.tail κ) (j := j + 1)
      have hleft : j + (w.stateArity + 1) = (j + 1) + w.stateArity := by omega
      have hright : j + (w.stateArity + 1 + w.selectedSum (Fin.tail κ)) =
          (j + 1) + w.flowParameterOrder (Fin.tail κ) := by
        simp only [StateAngleWord.flowParameterOrder]
        omega
      change parameterHeightWeight H (j + (w.stateArity + 1)) *
        w.selectedProduct (fun i => parameterHeightWeight H (κ i.succ)) ≤
          L ^ (n + 1) * parameterHeightWeight H
            (j + (w.stateArity + 1 + w.selectedSum (Fin.tail κ)))
      rw [hleft, hright]
      exact hh.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hL (Nat.le_succ n))
        (parameterHeightWeight_nonneg hH _))
  | @angle n w ih =>
      have hh := ih (κ := Fin.tail κ) (j := j)
      have hmerge := n01c_parameterHeightWeight_mul_le hH hHL hL
        (j + w.flowParameterOrder (Fin.tail κ)) (κ 0)
      have he : j + w.flowParameterOrder (Fin.tail κ) + κ 0 =
          j + (w.stateArity + (κ 0 + w.selectedSum (Fin.tail κ))) := by
        simp only [StateAngleWord.flowParameterOrder]
        omega
      change parameterHeightWeight H (j + w.stateArity) *
        (parameterHeightWeight H (κ 0) *
          w.selectedProduct (fun i => parameterHeightWeight H (κ i.succ))) ≤
        L ^ (n + 1) * parameterHeightWeight H
          (j + (w.stateArity + (κ 0 + w.selectedSum (Fin.tail κ))))
      calc
        _ = (parameterHeightWeight H (j + w.stateArity) *
            w.selectedProduct (fun i => parameterHeightWeight H (κ i.succ))) *
              parameterHeightWeight H (κ 0) := by ring
        _ ≤ (L ^ n * parameterHeightWeight H
            (j + w.flowParameterOrder (Fin.tail κ))) *
              parameterHeightWeight H (κ 0) :=
          mul_le_mul_of_nonneg_right hh (parameterHeightWeight_nonneg hH _)
        _ = L ^ n * (parameterHeightWeight H
            (j + w.flowParameterOrder (Fin.tail κ)) *
              parameterHeightWeight H (κ 0)) := by ring
        _ ≤ L ^ n * (L * parameterHeightWeight H
            (j + w.flowParameterOrder (Fin.tail κ) + κ 0)) :=
          mul_le_mul_of_nonneg_left hmerge (pow_nonneg (zero_le_one.trans hL) n)
        _ = _ := by rw [he, pow_succ, mul_assoc]

end ContinuousFlexibility.Analysis
