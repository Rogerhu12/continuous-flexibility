import ContinuousFlexibility.Analysis.N05SchurMembership
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The operator defined by a Schur-bounded matrix of actual blocks

Each output coordinate is the convergent series of the given blocks.
The Schur membership theorem places these coordinates in the target lp
space, after which the same bound makes their linear map continuous.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators ENNReal

section Blocks

variable {E F : ℕ → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace ℝ (E m)]
  [∀ k, NormedAddCommGroup (F k)] [∀ k, NormedSpace ℝ (F k)]
  [∀ k, CompleteSpace (F k)]
  (K : ∀ k m, E m →ₗ[ℝ] F k) (a : ℕ → ℕ → ℝ)
  (ha : ∀ k m, 0 ≤ a k m)
  (hrow : ∀ k, Summable (fun m => a k m))
  (hK : ∀ k m u, ‖K k m u‖ ≤ a k m * ‖u‖)

include ha hrow in
theorem n05SchurBlock_scalar_summable (x : lp E 2) (k : ℕ) :
    Summable (fun m => a k m * ‖x m‖) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (ha k m) (norm_nonneg _))
    (fun m => mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by norm_num) x m) (ha k m))
    ((hrow k).mul_right ‖x‖)

include ha hrow hK in
theorem n05SchurBlock_norm_summable (x : lp E 2) (k : ℕ) :
    Summable (fun m => ‖K k m (x m)‖) :=
  Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hK k m (x m))
    (n05SchurBlock_scalar_summable a ha hrow x k)

include ha hrow hK in
theorem n05SchurBlock_summable (x : lp E 2) (k : ℕ) :
    Summable (fun m => K k m (x m)) :=
  Summable.of_norm (n05SchurBlock_norm_summable K a ha hrow hK x k)

def n05SchurBlockValue (x : lp E 2) (k : ℕ) : F k :=
  ∑' m, K k m (x m)

include ha hrow hK in
theorem n05SchurBlockValue_bound (x : lp E 2) (k : ℕ) :
    ‖n05SchurBlockValue K x k‖ ≤ ∑' m, a k m * ‖x m‖ := by
  apply (norm_tsum_le_tsum_norm
    (n05SchurBlock_norm_summable K a ha hrow hK x k)).trans
  exact (n05SchurBlock_norm_summable K a ha hrow hK x k).tsum_le_tsum
    (fun m => hK k m (x m)) (n05SchurBlock_scalar_summable a ha hrow x k)

include ha hrow hK in
theorem n05SchurBlockValue_add (x y : lp E 2) (k : ℕ) :
    n05SchurBlockValue K (x + y) k =
      n05SchurBlockValue K x k + n05SchurBlockValue K y k := by
  simp only [n05SchurBlockValue, lp.coeFn_add, Pi.add_apply, map_add]
  exact (n05SchurBlock_summable K a ha hrow hK x k).tsum_add
    (n05SchurBlock_summable K a ha hrow hK y k)

include ha hrow hK in
theorem n05SchurBlockValue_smul (c : ℝ) (x : lp E 2) (k : ℕ) :
    n05SchurBlockValue K (c • x) k = c • n05SchurBlockValue K x k := by
  simp only [n05SchurBlockValue, lp.coeFn_smul, Pi.smul_apply, map_smul]
  exact (n05SchurBlock_summable K a ha hrow hK x k).tsum_const_smul c

end Blocks

section Operator

variable {E F : ℕ → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace ℝ (E m)]
  [∀ k, NormedAddCommGroup (F k)] [∀ k, NormedSpace ℝ (F k)]
  [∀ k, CompleteSpace (F k)]
  (K : ∀ k m, E m →ₗ[ℝ] F k) (a : ℕ → ℕ → ℝ)
  (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
  (ha : ∀ k m, 0 ≤ a k m)
  (hrow : ∀ k, Summable (fun m => a k m) ∧ ∑' m, a k m ≤ A)
  (hcol : ∀ m, Summable (fun k => a k m) ∧ ∑' k, a k m ≤ B)
  (hK : ∀ k m u, ‖K k m u‖ ≤ a k m * ‖u‖)

def n05SchurBlockLinear : lp E 2 →ₗ[ℝ] lp F 2 where
  toFun x := ⟨n05SchurBlockValue K x,
    n05_schur_memℓp a hA hB ha hrow hcol x (n05SchurBlockValue K x)
      (n05SchurBlockValue_bound K a ha (fun k => (hrow k).1) hK x)⟩
  map_add' := by
    intro x y
    apply lp.ext
    funext k
    exact n05SchurBlockValue_add K a ha (fun k => (hrow k).1) hK x y k
  map_smul' := by
    intro c x
    apply lp.ext
    funext k
    exact n05SchurBlockValue_smul K a ha (fun k => (hrow k).1) hK c x k

@[simp] theorem n05SchurBlockLinear_apply (x : lp E 2) (k : ℕ) :
    n05SchurBlockLinear K a A B hA hB ha hrow hcol hK x k =
      n05SchurBlockValue K x k := rfl

theorem n05SchurBlockLinear_bound (x : lp E 2) :
    ‖n05SchurBlockLinear K a A B hA hB ha hrow hcol hK x‖ ≤
      Real.sqrt (A * B) * ‖x‖ := by
  apply n05_schur_lp_norm a hA hB ha hrow hcol
  intro k
  rw [n05SchurBlockLinear_apply]
  exact n05SchurBlockValue_bound K a ha (fun k => (hrow k).1) hK x k

def n05SchurBlockOperator : lp E 2 →L[ℝ] lp F 2 :=
  (n05SchurBlockLinear K a A B hA hB ha hrow hcol hK).mkContinuous
    (Real.sqrt (A * B)) (n05SchurBlockLinear_bound K a A B hA hB ha hrow hcol hK)

theorem n05SchurBlockOperator_apply (x : lp E 2) (k : ℕ) :
    n05SchurBlockOperator K a A B hA hB ha hrow hcol hK x k =
      ∑' m, K k m (x m) := by
  rw [n05SchurBlockOperator, LinearMap.mkContinuous_apply,
    n05SchurBlockLinear_apply, n05SchurBlockValue]

theorem n05SchurBlockOperator_bound (x : lp E 2) :
    ‖n05SchurBlockOperator K a A B hA hB ha hrow hcol hK x‖ ≤
      Real.sqrt (A * B) * ‖x‖ :=
  n05SchurBlockLinear_bound K a A B hA hB ha hrow hcol hK x

end Operator

end ContinuousFlexibility.Analysis
