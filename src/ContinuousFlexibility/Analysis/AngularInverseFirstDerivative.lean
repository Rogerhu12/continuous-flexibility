import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
import ContinuousFlexibility.Analysis.CylinderSobolev
import ContinuousFlexibility.Geometry.GraphSurfaceGeometry

/-!
# Actual first derivative bounds for the angular inverse

The inverse derivative is obtained by differentiating the genuine
right-inverse identity. Its norm is controlled by the original radial
derivative and the positive original angular derivative. These are the
low-order inputs needed by the existing nonlinear inverse-jet estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem fderiv_parameterizedCircleInverse_apply
    {φ : PolarPoint → ℝ} {T : ℝ} (hT : T ≠ 0) (hφ : ContDiff ℝ ∞ φ)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T) (p v : PolarPoint) :
    fderiv ℝ (parameterizedCircleInverse φ) p v =
      (v.2 - radialPartial φ (p.1, parameterizedCircleInverse φ p) * v.1) /
        angularPartial φ (p.1, parameterizedCircleInverse φ p) := by
  let A := parameterizedCircleInverse φ
  have hA : ContDiff ℝ ∞ A :=
    contDiff_parameterizedCircleInverse hT hφ hpositive hperiod
  have hG : HasFDerivAt (fun q : PolarPoint => (q.1, A q))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ A p)) p :=
    hasFDerivAt_fst.prodMk (hA.differentiable (by simp) p).hasFDerivAt
  have hc := (hφ.differentiable (by simp) (p.1, A p)).hasFDerivAt.comp p hG
  have he : φ ∘ (fun q : PolarPoint => (q.1, A q)) = Prod.snd := by
    funext q
    exact parameterizedCircleInverse_right_inverse hT hφ hperiod q
  rw [he] at hc
  have hsnd : HasFDerivAt (fun q : PolarPoint => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hd := hc.unique hsnd
  have hv := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L v) hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at hv
  rw [height_fderiv_coordinates] at hv
  have ha : 0 < angularPartial φ (p.1, A p) := by
    rw [← deriv_cylinder_angular_slice (hφ.differentiable (by simp)) p.1 (A p)]
    exact hpositive (p.1, A p)
  apply (eq_div_iff ha.ne').mpr
  linarith only [hv]

theorem norm_fderiv_parameterizedCircleInverse_le
    {φ : PolarPoint → ℝ} {T κ M : ℝ} (hT : T ≠ 0) (hφ : ContDiff ℝ ∞ φ)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)
    (hκ : 0 < κ) (hM : 0 ≤ M) (p : PolarPoint)
    (hangle : κ ≤ angularPartial φ (p.1, parameterizedCircleInverse φ p))
    (hradial : |radialPartial φ (p.1, parameterizedCircleInverse φ p)| ≤ M) :
    ‖fderiv ℝ (parameterizedCircleInverse φ) p‖ ≤ (1 + M) / κ := by
  have hscale : 0 ≤ (1 + M) / κ := div_nonneg (by linarith) hκ.le
  apply ContinuousLinearMap.opNorm_le_bound _ hscale
  intro v
  rw [fderiv_parameterizedCircleInverse_apply hT hφ hpositive hperiod,
    Real.norm_eq_abs, abs_div, abs_of_pos (hκ.trans_le hangle)]
  apply (div_le_iff₀ (hκ.trans_le hangle)).mpr
  have hvfst : |v.1| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_fst_le v
  have hvsnd : |v.2| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_snd_le v
  have hnum :
      |v.2 - radialPartial φ (p.1, parameterizedCircleInverse φ p) * v.1| ≤
        (1 + M) * ‖v‖ := by
    calc
      _ ≤ |v.2| + |radialPartial φ (p.1, parameterizedCircleInverse φ p) * v.1| :=
        by simpa only [Real.norm_eq_abs] using
          norm_sub_le v.2 (radialPartial φ (p.1, parameterizedCircleInverse φ p) * v.1)
      _ = |v.2| + |radialPartial φ (p.1, parameterizedCircleInverse φ p)| * |v.1| := by
        rw [abs_mul]
      _ ≤ ‖v‖ + M * ‖v‖ :=
        add_le_add hvsnd (mul_le_mul hradial hvfst (abs_nonneg _) hM)
      _ = _ := by ring
  have hc : 1 + M ≤
      ((1 + M) / κ) * angularPartial φ (p.1, parameterizedCircleInverse φ p) := by
    calc
      _ = ((1 + M) / κ) * κ := (div_mul_cancel₀ _ hκ.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hangle hscale
  exact hnum.trans (by
    simpa only [mul_assoc, mul_comm ‖v‖] using
      mul_le_mul_of_nonneg_right hc (norm_nonneg v))

end ContinuousFlexibility.Analysis

