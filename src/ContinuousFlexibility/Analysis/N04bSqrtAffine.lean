import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum

/-!
# An affine optical radicand cannot cross zero smoothly

A differentiable square root at zero would give derivative zero for its
square. On the nonnegative half-line that square is the identity, whose
one-sided derivative is one. An invertible affine change of parameter
gives the same obstruction at every nonconstant affine zero.
-/

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set

theorem n04b_sqrt_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ Real.sqrt (0 : ℝ) := by
  intro h
  have hsquare : HasDerivAt (fun t : ℝ => (Real.sqrt t) ^ 2) 0 (0 : ℝ) := by
    convert! (hasDerivAt_pow 2 (Real.sqrt (0 : ℝ))).comp (0 : ℝ) h.hasDerivAt using 1 <;>
      norm_num
  have hid : HasDerivWithinAt (fun t : ℝ => t) 0 (Ici (0 : ℝ)) 0 :=
    hsquare.hasDerivWithinAt.congr_of_mem
      (fun t ht => (Real.sq_sqrt ht).symm)
      (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
  have hzero : derivWithin (fun t : ℝ => t) (Ici (0 : ℝ)) 0 = 0 :=
    hid.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  have hone : derivWithin (fun t : ℝ => t) (Ici (0 : ℝ)) 0 = 1 :=
    (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))
  exact zero_ne_one (hzero.symm.trans hone)

theorem n04b_sqrt_affine_not_differentiableAt_zero
    {a b t₀ : ℝ} (hzero : a + b * t₀ = 0) (hb : b ≠ 0) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (a + b * t)) t₀ := by
  intro h
  have hconst : HasDerivAt (fun _ : ℝ => t₀) (0 : ℝ) (0 : ℝ) :=
    hasDerivAt_const (0 : ℝ) t₀
  have hlinear : HasDerivAt (fun u : ℝ => b⁻¹ * u) b⁻¹ (0 : ℝ) :=
    hasDerivAt_const_mul b⁻¹
  have hparameterDeriv : HasDerivAt (fun u : ℝ => t₀ + b⁻¹ * u) b⁻¹ (0 : ℝ) := by
    simpa only [Pi.add_apply, zero_add] using! (HasDerivAt.add hconst hlinear)
  have hparameter : DifferentiableAt ℝ (fun u : ℝ => t₀ + b⁻¹ * u) (0 : ℝ) :=
    hparameterDeriv.differentiableAt
  have houter : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (a + b * t))
      (t₀ + b⁻¹ * 0) := by
    simpa only [mul_zero, add_zero] using h
  have hcomposition := houter.comp (0 : ℝ) hparameter
  have haffine (u : ℝ) : a + b * (t₀ + b⁻¹ * u) = u := by
    calc
      a + b * (t₀ + b⁻¹ * u) = (a + b * t₀) + (b * b⁻¹) * u := by ring
      _ = u := by rw [hzero, mul_inv_cancel₀ hb, one_mul, zero_add]
  apply n04b_sqrt_not_differentiableAt_zero
  simpa only [Function.comp_def, haffine] using hcomposition

theorem n04b_sqrt_affine_slope_eq_zero_of_differentiableAt
    {a b t₀ : ℝ} (hzero : a + b * t₀ = 0)
    (h : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (a + b * t)) t₀) :
    b = 0 := by
  by_contra hb
  exact n04b_sqrt_affine_not_differentiableAt_zero hzero hb h

end ContinuousFlexibility.Analysis
