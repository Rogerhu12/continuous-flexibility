import ContinuousFlexibility.Analysis.N07bMaterialAngularChain

/-!
# Square-root normalization of the actual inverse angular derivative

The square-root derivative is obtained by differentiating its actual
square on a positive neighborhood. Thus the normalization identity uses
the genuine differential and only local differentiability and positivity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n07b_inverseAngle_const_mul (Ψ : PolarPoint → PolarPoint) (a : ℝ)
    {g : PolarPoint → ℝ} {x : PolarPoint} (hg : DifferentiableAt ℝ g x) :
    n07bInverseAngleDerivative Ψ (fun y => a * g y) x =
      a * n07bInverseAngleDerivative Ψ g x := by
  rw [n07b_inverseAngle_mul Ψ differentiableAt_const hg]
  simp [n07bInverseAngleDerivative, radialPartial, angularPartial]

/-- The actual square-root derivative in the inverse angular direction. -/
theorem n07b_inverseAngle_sqrt (Ψ : PolarPoint → PolarPoint)
    {Ω : PolarPoint → ℝ} {x : PolarPoint}
    (hΩ : DifferentiableAt ℝ Ω x) (hpos : 0 < Ω x) :
    n07bInverseAngleDerivative Ψ (fun y => Real.sqrt (Ω y)) x =
      n07bInverseAngleDerivative Ψ Ω x / (2 * Real.sqrt (Ω x)) := by
  have hs := hΩ.sqrt hpos.ne'
  have heq : (fun y => Real.sqrt (Ω y) * Real.sqrt (Ω y)) =ᶠ[𝓝 x] Ω := by
    filter_upwards [hΩ.continuousAt.eventually (gt_mem_nhds hpos)] with y hy
    exact Real.mul_self_sqrt hy.le
  have hd : n07bInverseAngleDerivative Ψ
      (fun y => Real.sqrt (Ω y) * Real.sqrt (Ω y)) x =
        n07bInverseAngleDerivative Ψ Ω x := by
    rw [n07b_inverseAngle_eq_fderiv, n07b_inverseAngle_eq_fderiv]
    exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (n07bInverseAngleVector Ψ x))
      (heq.fderiv_eq (𝕜 := ℝ))
  rw [n07b_inverseAngle_mul Ψ hs hs] at hd
  apply (eq_div_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hpos).ne')).mpr
  calc
    _ = n07bInverseAngleDerivative Ψ (fun y => Real.sqrt (Ω y)) x * Real.sqrt (Ω x) +
        Real.sqrt (Ω x) * n07bInverseAngleDerivative Ψ (fun y => Real.sqrt (Ω y)) x := by ring
    _ = _ := hd

/-- Conjugating the actual direction by the square root of a positive
density creates exactly its logarithmic half-density coefficient. -/
theorem n07b_inverseAngle_sqrt_conjugation (Ψ : PolarPoint → PolarPoint)
    {Ω g : PolarPoint → ℝ} {x : PolarPoint}
    (hΩ : DifferentiableAt ℝ Ω x) (hpos : 0 < Ω x)
    (hg : DifferentiableAt ℝ g x) :
    Real.sqrt (Ω x) * n07bInverseAngleDerivative Ψ g x =
      n07bInverseAngleDerivative Ψ (fun y => Real.sqrt (Ω y) * g y) x +
        (-n07bInverseAngleDerivative Ψ Ω x / (2 * Ω x)) *
          (Real.sqrt (Ω x) * g x) := by
  rw [n07b_inverseAngle_mul Ψ (hΩ.sqrt hpos.ne') hg,
    n07b_inverseAngle_sqrt Ψ hΩ hpos]
  let s : ℝ := Real.sqrt (Ω x)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsquare : s ^ 2 = Ω x := Real.sq_sqrt hpos.le
  change s * n07bInverseAngleDerivative Ψ g x =
    n07bInverseAngleDerivative Ψ Ω x / (2 * s) * g x +
      s * n07bInverseAngleDerivative Ψ g x +
        (-n07bInverseAngleDerivative Ψ Ω x / (2 * Ω x)) * (s * g x)
  rw [← hsquare]
  field_simp [hs] <;> ring

end ContinuousFlexibility.Analysis
