import ContinuousFlexibility.Statements.Nonlinear

/-!
# Uniform coordinate maps on the canonical Hilbert sequence spaces

The maps are formed coordinate by coordinate in the actual lp spaces.
Their norm estimate is the pointwise norm comparison with a constant
multiple of the input, and does not use a completion chosen by an inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology

section CoordinateMaps

variable {E F : ℕ → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace ℝ (E m)]
  [∀ m, NormedAddCommGroup (F m)] [∀ m, NormedSpace ℝ (F m)]

def n05LpMapLinear (A : ∀ m, E m →ₗ[ℝ] F m) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ m x, ‖A m x‖ ≤ B * ‖x‖) : lp E 2 →ₗ[ℝ] lp F 2 where
  toFun := fun u => ⟨fun m => A m (u m), by
    apply ((lp.memℓp u).const_smul B).mono'
    intro m
    simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hB]
      using hA m (u m)⟩
  map_add' := by
    intro u v
    apply lp.ext
    funext m
    simp only [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' := by
    intro c u
    apply lp.ext
    funext m
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem n05LpMapLinear_apply (A : ∀ m, E m →ₗ[ℝ] F m) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ m x, ‖A m x‖ ≤ B * ‖x‖) (u : lp E 2) (m : ℕ) :
    n05LpMapLinear A B hB hA u m = A m (u m) := rfl

theorem n05LpMapLinear_bound (A : ∀ m, E m →ₗ[ℝ] F m) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ m x, ‖A m x‖ ≤ B * ‖x‖) (u : lp E 2) :
    ‖n05LpMapLinear A B hB hA u‖ ≤ B * ‖u‖ := by
  calc
    ‖n05LpMapLinear A B hB hA u‖ ≤ ‖B • u‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro m
      simpa only [n05LpMapLinear_apply, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hB] using hA m (u m)
    _ = B * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hB]

def n05LpMapCLM (A : ∀ m, E m →ₗ[ℝ] F m) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ m x, ‖A m x‖ ≤ B * ‖x‖) : lp E 2 →L[ℝ] lp F 2 :=
  (n05LpMapLinear A B hB hA).mkContinuous B (n05LpMapLinear_bound A B hB hA)

theorem n05LpMapCLM_apply (A : ∀ m, E m →ₗ[ℝ] F m) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ m x, ‖A m x‖ ≤ B * ‖x‖) (u : lp E 2) (m : ℕ) :
    n05LpMapCLM A B hB hA u m = A m (u m) := by
  rw [n05LpMapCLM, LinearMap.mkContinuous_apply, n05LpMapLinear_apply]

theorem n05LpMapCLM_bound (A : ∀ m, E m →ₗ[ℝ] F m) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ m x, ‖A m x‖ ≤ B * ‖x‖) (u : lp E 2) :
    ‖n05LpMapCLM A B hB hA u‖ ≤ B * ‖u‖ :=
  n05LpMapLinear_bound A B hB hA u

end CoordinateMaps

end ContinuousFlexibility.Statements
