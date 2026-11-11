import ContinuousFlexibility.Statements.Analysis
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparing weights on a material-coordinate window

The first material derivative of the logarithm becomes the ordinary
derivative after pulling back by the actual radius. Thus the weights at
any two points of a unit material window are uniformly comparable.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem hasDerivAt_material_log_pullback {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Ioo D.a D.b))
    (hpos : ∀ r ∈ Ioo D.a D.b, 0 < w r) (x : ℝ) :
    HasDerivAt (fun y => Real.log (w (T.radius y)))
      (materialDerivative T (fun r => Real.log (w r)) (T.radius x)) x := by
  obtain ⟨_, _, _, _, _, _, _, hinside, _, hderiv, _⟩ := hT
  have hr := (hinside x).1
  have hlog : DifferentiableAt ℝ (fun r => Real.log (w r)) (T.radius x) :=
    (((hw _ hr).contDiffAt (isOpen_Ioo.mem_nhds hr)).log (hpos _ hr).ne').differentiableAt
      (by simp)
  change HasDerivAt ((fun r : ℝ => Real.log (w r)) ∘ T.radius)
    (T.ell (T.radius x) * deriv (fun r => Real.log (w r)) (T.radius x)) x
  rw [mul_comm]
  exact hlog.hasDerivAt.comp x (hderiv x)

/-- A material logarithmic derivative bound becomes a global derivative
bound in the actual material coordinate. -/
theorem material_M_log_derivative_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 ≤ C ∧ Differentiable ℝ (fun x => Real.log (T.M (T.radius x))) ∧
      ∀ x, |deriv (fun y => Real.log (T.M (T.radius y))) x| ≤ C := by
  have h := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, hinside, _, _, _, _, _, hlog, _⟩ := h
  have hm : ContDiffOn ℝ ∞ T.M (Ioo D.a D.b) := hcont T.M (by simp)
  have hpositive (r : ℝ) (hr : r ∈ Ioo D.a D.b) : 0 < T.M r :=
    zero_lt_one.trans_le (hpos r hr).2.2.2
  obtain ⟨C, hC, hbound⟩ := hlog 1 (by decide)
  have hderiv := hasDerivAt_material_log_pullback hT hm hpositive
  refine ⟨C, hC, fun x => (hderiv x).differentiableAt, fun x => ?_⟩
  rw [(hderiv x).deriv]
  simpa only [materialDerivativeIterate, Function.iterate_one] using
    (hbound (T.radius x) (hinside x).1).2.1

/-- The same comparison constant works for every unit interval. Each
nonnegative weight power has its explicit exponential comparison factor. -/
theorem material_M_unit_window_comparison {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ), 0 ≤ c → ∀ x y : ℝ, |x - y| ≤ 1 →
      T.M (T.radius x) ^ c ≤ Real.exp (c * C) * T.M (T.radius y) ^ c := by
  obtain ⟨C, hC, hdiff, hbound⟩ := material_M_log_derivative_bound hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  have hp (x : ℝ) : 0 < T.M (T.radius x) :=
    zero_lt_one.trans_le (hpos _ (hinside x).1).2.2.2
  refine ⟨C, hC, fun c hc x y hxy => ?_⟩
  have hb : |Real.log (T.M (T.radius x)) - Real.log (T.M (T.radius y))| ≤ C * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z _ => hdiff z) (fun z _ => by simpa only [Real.norm_eq_abs] using hbound z)
        (mem_univ y) (mem_univ x)
  have hlog : Real.log (T.M (T.radius x)) ≤ Real.log (T.M (T.radius y)) + C := by
    have hh := (le_abs_self _).trans (hb.trans ((mul_le_mul_of_nonneg_left hxy hC).trans_eq
      (mul_one C)))
    linarith only [hh]
  calc
    T.M (T.radius x) ^ c = Real.exp (Real.log (T.M (T.radius x)) * c) := by
      rw [Real.exp_mul, Real.exp_log (hp x)]
    _ ≤ Real.exp ((Real.log (T.M (T.radius y)) + C) * c) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog hc)
    _ = Real.exp (c * C) * T.M (T.radius y) ^ c := by
      rw [add_mul, Real.exp_add, Real.exp_mul, Real.exp_log (hp y)]
      rw [mul_comm C c, mul_comm]

end ContinuousFlexibility.Statements
