module

public import ContinuousFlexibility.Analysis.LogPolynomialEnvelope
public import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds

/-!
# Scalar kernels for the actual logarithmic height traces

The existing logarithm envelope is applied to the identity map. This
controls every scalar outer derivative used by the finite root-trace
construction from the actual height value and its reciprocal. The
exponential retains its actual amplitude at every outer order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Realization_log_outer_derivatives (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M y : ℝ, 1 ≤ M → 0 < y → y ≤ M → y⁻¹ ≤ M →
      ∀ a b : ℕ, a + b ≤ N →
      ‖iteratedFDeriv ℝ a (iteratedDeriv b Real.log) y‖ ≤ C * M ^ (2 * N + 1) := by
  obtain ⟨C, hC, hb⟩ := exists_log_finiteJet_polynomial_envelope (E := ℝ) N
  refine ⟨C, hC, ?_⟩
  intro M y hM hy hyM hinv a b hab
  have hid (j : ℕ) (hj : 1 ≤ j) (_hjn : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun x : ℝ => x) y‖ ≤ M := by
    have h : |iteratedDeriv j (fun x : ℝ => x) y| ≤ 1 := by
      rw [iteratedDeriv_fun_id, if_neg (by omega : j ≠ 0)]
      split_ifs <;> norm_num
    have hnorm : ‖iteratedFDeriv ℝ j (fun x : ℝ => x) y‖ ≤ 1 := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using h
    exact hnorm.trans hM
  have h := hb hM (fun x : ℝ => x) y contDiffAt_id hy hyM hinv hid (a + b) hab
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    circle_iteratedDeriv_iteratedDeriv] using h

theorem n04Realization_exp_outer_derivatives (a b : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ a (iteratedDeriv b Real.exp) y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, circle_iteratedDeriv_iteratedDeriv]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

end ContinuousFlexibility.Analysis
