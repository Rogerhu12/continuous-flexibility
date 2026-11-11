import ContinuousFlexibility.Analysis.SmoothDirectionsLimitAssembly
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Uniform seminorm bounds for directional jet families

The first extra jet controls variation of the base point by the mean
value theorem. Multilinearity controls variation of the directions.
Both estimates use continuous seminorms, so they apply to the original
locally convex space without replacing it by a normed completion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def multilinearDifferenceTuple {n : ℕ} (v w : Fin n → E) (i j : Fin n) : E :=
  if j < i then w j else if i = j then w j - v j else v j

theorem multilinear_sub_eq_sum {n : ℕ} (A : E [×n]→L[ℝ] ℝ) (v w : Fin n → E) :
    A w - A v = ∑ i : Fin n, A (multilinearDifferenceTuple v w i) := by
  simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies,
    multilinearDifferenceTuple] using
    A.toMultilinearMap.map_sub_map_piecewise w v Finset.univ

def seminormMultilinearDifference {n : ℕ} (p : Seminorm ℝ E) (v w : Fin n → E) : ℝ :=
  ∑ i : Fin n, ∏ j : Fin n, p (multilinearDifferenceTuple v w i j)

theorem seminormMultilinearDifference_self {n : ℕ}
    (p : Seminorm ℝ E) (v : Fin n → E) : seminormMultilinearDifference p v v = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [multilinearDifferenceTuple, lt_self_iff_false, if_false, if_true, sub_self, map_zero]

theorem continuous_seminormMultilinearDifference {n : ℕ}
    (p : Seminorm ℝ E) (hp : Continuous p) (v : Fin n → E) :
    Continuous (seminormMultilinearDifference p v) := by
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetProd
  intro j hj
  unfold multilinearDifferenceTuple
  split_ifs
  · exact hp.comp (continuous_apply j)
  · exact hp.comp ((continuous_apply j).sub continuous_const)
  · exact continuous_const

theorem abs_multilinear_sub_le_of_seminorm_bound {n : ℕ}
    (A : E [×n]→L[ℝ] ℝ) (p : Seminorm ℝ E) (B : ℝ)
    (hbound : ∀ v : Fin n → E, |A v| ≤ B * ∏ i, p (v i))
    (v w : Fin n → E) :
    |A w - A v| ≤ B * seminormMultilinearDifference p v w := by
  rw [multilinear_sub_eq_sum]
  calc
    |∑ i : Fin n, A (multilinearDifferenceTuple v w i)| ≤
        ∑ i : Fin n, |A (multilinearDifferenceTuple v w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, B * ∏ j : Fin n, p (multilinearDifferenceTuple v w i j) :=
      Finset.sum_le_sum (fun i hi => hbound _)
    _ = B * seminormMultilinearDifference p v w := (Finset.mul_sum _ _ _).symm

theorem seminorm_affine_segment_le (p : Seminorm ℝ E) (x y : E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p (x + t • (y - x)) ≤ p x + p (y - x) := by
  calc
    p (x + t • (y - x)) ≤ p x + p (t • (y - x)) := map_add_le_add _ _ _
    _ = p x + |t| * p (y - x) := by rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ p x + p (y - x) := by
      rw [abs_of_nonneg ht.1]
      exact add_le_add_left (mul_le_of_le_one_left (apply_nonneg _ _) ht.2) _

theorem SmoothDirections.base_variation_le
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f) (hU : Convex ℝ U)
    {n : ℕ} (p : Seminorm ℝ E) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ y ∈ U, ∀ v : Fin (n + 1) → E,
      |J.D (n + 1) y v| ≤ B * (1 + p y) * ∏ i, p (v i))
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (v : Fin n → E) :
    |J.D n y v - J.D n x v| ≤
      B * (1 + p x + p (y - x)) * (p (y - x) * ∏ i, p (v i)) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ U := by
    have hm := hU hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    convert hm using 1 <;> module
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s => J.D n (x + s • (y - x)) v)
        (J.D (n + 1) (x + t • (y - x)) (Fin.cons (y - x) v)) (Icc (0 : ℝ) 1) t :=
    (J.hasDerivAt_line_jet x (y - x) n v (hmem t ht)).hasDerivWithinAt
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖J.D (n + 1) (x + t • (y - x)) (Fin.cons (y - x) v)‖ ≤
        B * (1 + p x + p (y - x)) * (p (y - x) * ∏ i, p (v i)) := by
    rw [Real.norm_eq_abs]
    have hb := hbound _ (hmem t ht) (Fin.cons (y - x) v)
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [seminorm_affine_segment_le p x y ht]) hB)
      (mul_nonneg (apply_nonneg _ _) (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv
    (fun t ht => hnorm t ⟨ht.1, ht.2.le⟩)
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel, Real.norm_eq_abs] using hm

end ContinuousFlexibility.Analysis
