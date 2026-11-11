import ContinuousFlexibility.Analysis.ProjectiveDifferential
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A smooth optical square root cannot cross its type boundary

If an affine radicand has a differentiable square root throughout a real
parameter interval, its zero cannot lie inside that interval. This elementary
fact turns genuine parameter differentiability of the ordinary flow into a
relative bound for the controlled optical radicand.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem n08_not_differentiableAt_sqrt_zero :
    ¬ DifferentiableAt ℝ Real.sqrt 0 := by
  intro h
  have hd : DifferentiableAt ℝ (fun x : ℝ => 2 * (Real.sqrt x) ^ 2 - x) 0 :=
    ((h.pow 2).const_mul 2).sub differentiableAt_id
  have heq : (fun x : ℝ => 2 * (Real.sqrt x) ^ 2 - x) = abs := by
    funext x
    rw [Real.sq_sqrt']
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · rw [max_eq_right (le_of_not_ge hx), abs_of_nonpos (le_of_not_ge hx)]
      ring
  rw [heq] at hd
  exact not_differentiableAt_abs_zero hd

theorem n08_sqrtAffine_radius_bound {A B R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hd : ∀ t : ℝ, |t| < R → DifferentiableAt ℝ
      (fun s : ℝ => Real.sqrt (A + s * B)) t) :
    R * |B| ≤ A := by
  by_cases hB : B = 0
  · simpa only [hB, abs_zero, mul_zero] using hA.le
  by_contra hnot
  have hlt : A < R * |B| := lt_of_not_ge hnot
  have ht : |(-A) / B| < R := by
    rw [abs_div, abs_neg, abs_of_pos hA]
    exact (div_lt_iff₀ (abs_pos.mpr hB)).mpr hlt
  have hroot := hd ((-A) / B) ht
  have hinv : DifferentiableAt ℝ (fun s : ℝ => (s - A) / B) 0 :=
    (differentiableAt_id.sub_const A).div_const B
  have hroot' : DifferentiableAt ℝ (fun s : ℝ => Real.sqrt (A + s * B))
      ((0 - A) / B) := by
    simpa only [zero_sub] using hroot
  have hcomp := hroot'.comp hinv
  have heq : (fun s : ℝ => Real.sqrt (A + ((s - A) / B) * B)) = Real.sqrt := by
    funext s
    rw [div_mul_cancel₀ _ hB]
    congr 1
    ring
  apply n08_not_differentiableAt_sqrt_zero
  simpa only [Function.comp_apply, heq] using hcomp

/-- Recenter the actual affine-line derivative at an arbitrary parameter. -/
theorem n08_hasDerivAt_affine_parameter
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : E → ℝ} {x v : E} {t d : ℝ}
    (hd : HasProjectiveLineDerivAt f d (x + t • v) v) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) d t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    zero_add, zero_smul, add_zero, add_smul, add_assoc] using hd

/-- A genuine directional tower and an exact optical formula give the
relative radicand bound; no type-preservation hypothesis is supplied. -/
theorem n08_sqrtAffine_bound_of_lineDerivatives
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (x v : E) {A B K R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hd : ∀ t : ℝ, |t| < R → ∃ d : ℝ,
      HasProjectiveLineDerivAt f d (x + t • v) v)
    (hf : ∀ t : ℝ, |t| < R → f (x + t • v) = K - Real.sqrt (A + t * B)) :
    R * |B| ≤ A := by
  apply n08_sqrtAffine_radius_bound hA hR
  intro t ht
  obtain ⟨d, hd⟩ := hd t ht
  have hg := (differentiableAt_const K).sub
    (n08_hasDerivAt_affine_parameter hd).differentiableAt
  apply hg.congr_of_eventuallyEq
  have hn : ∀ᶠ s : ℝ in 𝓝 t, |s| < R :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds ht
  filter_upwards [hn] with s hs
  rw [hf s hs]
  ring

end ContinuousFlexibility.Analysis
