import ContinuousFlexibility.Analysis.LocalJointJetSeminormBounds
import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Weighted bounds for the existing joint spatial expansion

The same scalar angular expansion is applied first to radius and then
to angle. A physical direction receives one prescribed spatial factor;
the parameter directions use their two supplied seminorm bounds. The
original mixed jets and the original multilinear expansion are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A weighted version of the existing scalar angular expansion. No
topology or norm on the parameter space enters this finite calculation. -/
theorem n04Realization_scalarAngularExpansion_weighted_bound
    (n : ℕ) (p : E → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : ScalarAngularJetData E) {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hA : ∀ a k : ℕ, a + k ≤ n → ∀ v : Fin k → E,
      |A a k v| ≤ C * t ^ a * ∏ i, p (v i))
    (v : Fin n → E × ℝ) :
    |scalarAngularExpansion n A v| ≤
      C * ∏ i, (p (v i).1 + t * |(v i).2|) := by
  induction n generalizing A C with
  | zero =>
      simpa only [scalarAngularExpansion_zero_apply, pow_zero,
        Fin.prod_univ_zero, mul_one] using hA 0 0 (by omega) Fin.elim0
  | succ n ih =>
      have hhead (a k : ℕ) (hak : a + k ≤ n) (u : Fin k → E) :
          |scalarAngularHead A (v 0) a k u| ≤
            (C * p (v 0).1) * t ^ a * ∏ i, p (u i) := by
        have h := hA a (k + 1) (by omega) (Fin.cons (v 0).1 u)
        simpa only [scalarAngularHead_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ, mul_assoc, mul_comm, mul_left_comm] using h
      have hshift (a k : ℕ) (hak : a + k ≤ n) (u : Fin k → E) :
          |scalarAngularShift A a k u| ≤
            (C * t) * t ^ a * ∏ i, p (u i) := by
        have h := hA (a + 1) k (by omega) u
        simpa only [scalarAngularShift_apply, pow_succ,
          mul_assoc, mul_comm, mul_left_comm] using h
      have hh := ih (scalarAngularHead A (v 0))
        (mul_nonneg hC (hp _)) hhead (Fin.tail v)
      have hs := ih (scalarAngularShift A) (mul_nonneg hC ht) hshift (Fin.tail v)
      rw [scalarAngularExpansion_succ_apply]
      calc
        _ ≤ |scalarAngularExpansion n (scalarAngularHead A (v 0)) (Fin.tail v)| +
            |(v 0).2| * |scalarAngularExpansion n (scalarAngularShift A) (Fin.tail v)| := by
          simpa only [abs_mul] using abs_add_le
            (scalarAngularExpansion n (scalarAngularHead A (v 0)) (Fin.tail v))
            ((v 0).2 * scalarAngularExpansion n (scalarAngularShift A) (Fin.tail v))
        _ ≤ (C * p (v 0).1) *
              ∏ i, (p (Fin.tail v i).1 + t * |(Fin.tail v i).2|) +
            |(v 0).2| * ((C * t) *
              ∏ i, (p (Fin.tail v i).1 + t * |(Fin.tail v i).2|)) :=
          add_le_add hh (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
        _ = _ := by rw [Fin.prod_univ_succ]; simp only [Fin.tail]; ring

/-- Applying the same expansion to both physical coordinates charges
exactly one spatial factor for each radial or angular derivative. -/
theorem n04Realization_doubleAngularExpansion_weighted_bound
    (n : ℕ) (p : E → ℝ) (hp : ∀ x, 0 ≤ p x)
    (A : ∀ a b k : ℕ, MultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hA : ∀ a b k : ℕ, a + b + k ≤ n → ∀ v : Fin k → E,
      |A a b k v| ≤ C * t ^ (a + b) * ∏ i, p (v i))
    (v : Fin n → (E × ℝ) × ℝ) :
    |scalarAngularExpansion n
      (fun b k => scalarAngularExpansion k (fun a j => A a b j)) v| ≤
      C * ∏ i, (p (v i).1.1 + t * |(v i).1.2| + t * |(v i).2|) := by
  apply n04Realization_scalarAngularExpansion_weighted_bound n
    (fun x : E × ℝ => p x.1 + t * |x.2|)
    (fun x => add_nonneg (hp x.1) (mul_nonneg ht (abs_nonneg x.2)))
    _ hC ht
  intro b k hbk u
  apply n04Realization_scalarAngularExpansion_weighted_bound k p hp
    (fun a j => A a b j) (mul_nonneg hC (pow_nonneg ht b)) ht
  intro a j haj w
  have h := hA a b j (by omega) w
  simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h

variable [TopologicalSpace E]

/-- The same multilinear map is normalized using the low bound and the
high bound divided by the chosen common scale. Kernels are handled by
the existing homogeneous normalization theorem. -/
theorem n04Realization_multilinear_twoSeminorm_bound
    {k : ℕ} (A : E [×k]→L[ℝ] ℝ) (low high : Seminorm ℝ E)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hA : ∀ v : Fin k → E, (∀ i, low (v i) ≤ 1) →
      (∀ i, high (v i) ≤ R) → |A v| ≤ C) (v : Fin k → E) :
    |A v| ≤ C * ∏ i, (low (v i) + high (v i) / R) := by
  let r : NNReal := ⟨R⁻¹, inv_nonneg.mpr hR.le⟩
  let q : Seminorm ℝ E := low + r • high
  have hscale (x : E) : (r • high) x = (r : ℝ) * high x :=
    (_root_.smul_apply r high x).trans
      ((NNReal.smul_def r (high x)).trans (smul_eq_mul (r : ℝ) (high x)))
  have hq (x : E) : q x = low x + high x / R := by
    calc
      q x = low x + (r • high) x := _root_.add_apply low (r • high) x
      _ = low x + (r : ℝ) * high x := congrArg (fun y : ℝ => low x + y) (hscale x)
      _ = low x + high x / R := by
        simp only [r, NNReal.coe_mk, div_eq_mul_inv, mul_comm]
  have hunit (u : Fin k → E) (hu : ∀ i, q (u i) < 1) :
      (normSeminorm ℝ ℝ) (A u) ≤
        C * ((1 : ℝ) + ∑ i : Fin k, (0 : Seminorm ℝ E) (u i)) := by
    have hlo (i : Fin k) : low (u i) ≤ 1 := by
      have h := hu i
      rw [hq] at h
      exact (le_add_of_nonneg_right (div_nonneg (apply_nonneg high _) hR.le)).trans h.le
    have hhi (i : Fin k) : high (u i) ≤ R := by
      have h := hu i
      rw [hq] at h
      have hd : high (u i) / R ≤ 1 :=
        (le_add_of_nonneg_left (apply_nonneg low _)).trans h.le
      exact (div_le_one hR).mp hd
    simpa only [coe_normSeminorm, Real.norm_eq_abs, zero_apply,
      Finset.sum_const_zero, add_zero, mul_one] using hA u hlo hhi
  have h := multilinear_bound_of_unitBall A (normSeminorm ℝ ℝ)
    q (0 : Seminorm ℝ E) hC hunit v
  simpa only [coe_normSeminorm, Real.norm_eq_abs, multilinearTameSize,
    zero_apply, zero_mul, Finset.sum_const_zero, one_mul, add_zero, hq] using h

end ContinuousFlexibility.Analysis
