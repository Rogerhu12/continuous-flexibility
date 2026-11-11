import ContinuousFlexibility.Geometry.GraphSurfaceGeometry
import ContinuousFlexibility.Geometry.MarkerBump

/-!
# The strict peak of the proposed cap marker

This file identifies the actual Gaussian curvature of the integral bump with
the explicit expression in `eq:marker-curvature`, Section 2, and proves its
strict global maximum. It does not yet construct the separated cap or compare
the marker with the rest of a closed surface.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The scalar expression displayed in `eq:marker-curvature`, extended by zero
outside the elliptic support. Its geometric identification is proved below. -/
def markerCurvatureExpression (A B k ρ : ℝ) (x : PolarPoint) : ℝ :=
  let ξ := A * x.1 ^ 2 + B * x.2 ^ 2
  if ξ < ρ ^ 2 then
    A * B * k ^ 2 * Real.exp (-2 * (ξ / (ρ ^ 2 - ξ))) *
      (1 - 2 * ξ * (ρ ^ 2 / (ρ ^ 2 - ξ) ^ 2)) /
      (1 + k ^ 2 * Real.exp (-2 * (ξ / (ρ ^ 2 - ξ))) *
        (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2)) ^ 2
  else 0

theorem markerCurvatureExpression_zero (A B k : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    markerCurvatureExpression A B k ρ 0 = A * B * k ^ 2 := by
  have hr := sq_pos_of_ne_zero hρ
  simp [markerCurvatureExpression, hr]

theorem markerCurvatureExpression_support {A B k ρ : ℝ} {x : PolarPoint}
    (hx : ρ ^ 2 ≤ A * x.1 ^ 2 + B * x.2 ^ 2) :
    markerCurvatureExpression A B k ρ x = 0 := by
  simp [markerCurvatureExpression, not_lt.mpr hx]

theorem positive_ellipticQuadratic_of_ne_zero {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {x : PolarPoint} (hx : x ≠ 0) : 0 < A * x.1 ^ 2 + B * x.2 ^ 2 := by
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := by
      intro h2
      exact hx (Prod.ext h1 h2)
    have := mul_pos hB (sq_pos_of_ne_zero h2)
    simpa [h1] using this
  · exact add_pos_of_pos_of_nonneg (mul_pos hA (sq_pos_of_ne_zero h1)) (by positivity)

/-- Strict inequality away from the center, including outside the support. -/
theorem markerCurvatureExpression_lt_peak {A B k ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hk : k ≠ 0) (hρ : ρ ≠ 0)
    {x : PolarPoint} (hx : x ≠ 0) :
    markerCurvatureExpression A B k ρ x < A * B * k ^ 2 := by
  have hC : 0 < A * B * k ^ 2 := mul_pos (mul_pos hA hB) (sq_pos_of_ne_zero hk)
  have hξ := positive_ellipticQuadratic_of_ne_zero hA hB hx
  dsimp [markerCurvatureExpression]
  split_ifs with hs
  · have hd : 0 < ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2) := sub_pos.mpr hs
    have hratio : 0 < (A * x.1 ^ 2 + B * x.2 ^ 2) /
        (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)) := div_pos hξ hd
    have he : Real.exp (-2 * ((A * x.1 ^ 2 + B * x.2 ^ 2) /
        (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)))) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hf : 1 - 2 * (A * x.1 ^ 2 + B * x.2 ^ 2) *
        (ρ ^ 2 / (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)) ^ 2) ≤ 1 := by
      have : 0 ≤ 2 * (A * x.1 ^ 2 + B * x.2 ^ 2) *
          (ρ ^ 2 / (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)) ^ 2) := by positivity
      linarith
    have hn : A * B * k ^ 2 * Real.exp (-2 * ((A * x.1 ^ 2 + B * x.2 ^ 2) /
        (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)))) *
        (1 - 2 * (A * x.1 ^ 2 + B * x.2 ^ 2) *
          (ρ ^ 2 / (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)) ^ 2)) <
        A * B * k ^ 2 := by
      calc
        _ ≤ A * B * k ^ 2 * Real.exp (-2 * ((A * x.1 ^ 2 + B * x.2 ^ 2) /
            (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)))) :=
          mul_le_of_le_one_right (by positivity) hf
        _ < A * B * k ^ 2 := mul_lt_of_lt_one_right hC he
    have hb : 1 ≤ 1 + k ^ 2 * Real.exp (-2 * ((A * x.1 ^ 2 + B * x.2 ^ 2) /
        (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)))) *
        (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2) := by
      have : 0 ≤ k ^ 2 * Real.exp (-2 * ((A * x.1 ^ 2 + B * x.2 ^ 2) /
          (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)))) *
          (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2) := by positivity
      linarith
    have hden : 1 ≤ (1 + k ^ 2 * Real.exp (-2 * ((A * x.1 ^ 2 + B * x.2 ^ 2) /
        (ρ ^ 2 - (A * x.1 ^ 2 + B * x.2 ^ 2)))) *
        (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2)) ^ 2 := by nlinarith
    apply (div_lt_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
    exact hn.trans_le (le_mul_of_one_le_right hC.le hden)
  · exact hC

theorem markerCurvatureExpression_le_peak {A B k ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hk : k ≠ 0) (hρ : ρ ≠ 0) (x : PolarPoint) :
    markerCurvatureExpression A B k ρ x ≤ A * B * k ^ 2 := by
  by_cases hx : x = 0
  · subst x
    exact (markerCurvatureExpression_zero A B k hρ).le
  · exact (markerCurvatureExpression_lt_peak hA hB hk hρ hx).le

theorem markerCurvatureExpression_eq_peak_iff {A B k ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hk : k ≠ 0) (hρ : ρ ≠ 0) (x : PolarPoint) :
    markerCurvatureExpression A B k ρ x = A * B * k ^ 2 ↔ x = 0 := by
  constructor
  · intro he
    by_contra hx
    exact (ne_of_lt (markerCurvatureExpression_lt_peak hA hB hk hρ hx)) he
  · intro hx
    subst x
    exact markerCurvatureExpression_zero A B k hρ

theorem graphHessian_markerBump_apply (A B k ρ : ℝ) (x : PolarPoint) (i j : Fin 2) :
    graphHessian (markerBump A B k ρ) x i j =
      -k * markerKernel ρ (markerQuadratic A B x) *
        (A * (surfaceBasis j).1 * (surfaceBasis i).1 +
          B * (surfaceBasis j).2 * (surfaceBasis i).2) -
      2 * k * deriv (markerKernel ρ) (markerQuadratic A B x) *
        (A * x.1 * (surfaceBasis j).1 + B * x.2 * (surfaceBasis j).2) *
        (A * x.1 * (surfaceBasis i).1 + B * x.2 * (surfaceBasis i).2) := by
  have hz : DifferentiableAt ℝ (fderiv ℝ (markerBump A B k ρ)) x :=
    ((contDiff_markerBump A B k ρ).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  unfold graphHessian
  rw [← polar_fderiv_partial hz]
  exact markerBump_secondDerivative A B k ρ x (surfaceBasis j) (surfaceBasis i)

theorem graphHessian_markerBump_det (A B k ρ : ℝ) (x : PolarPoint) :
    (graphHessian (markerBump A B k ρ) x).det =
      A * B * k ^ 2 * markerKernel ρ (markerQuadratic A B x) *
        (markerKernel ρ (markerQuadratic A B x) + 2 * markerQuadratic A B x *
          deriv (markerKernel ρ) (markerQuadratic A B x)) := by
  rw [Matrix.det_fin_two]
  simp only [graphHessian_markerBump_apply, surfaceBasis_zero, surfaceBasis_one,
    mul_zero, mul_one, zero_add, add_zero]
  unfold markerQuadratic
  ring

theorem graphAreaSq_markerBump (A B k ρ : ℝ) (x : PolarPoint) :
    graphAreaSq (markerBump A B k ρ) x =
      1 + k ^ 2 * markerKernel ρ (markerQuadratic A B x) ^ 2 *
        (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2) := by
  simp only [graphAreaSq, radialPartial, angularPartial, fderiv_markerBump_apply,
    mul_one, mul_zero, add_zero, zero_add]
  ring

theorem surfaceGaussianCurvature_markerBump_kernel (A B k ρ : ℝ) (x : PolarPoint) :
    surfaceGaussianCurvature (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) x) x =
    (A * B * k ^ 2 * markerKernel ρ (markerQuadratic A B x) *
      (markerKernel ρ (markerQuadratic A B x) + 2 * markerQuadratic A B x *
        deriv (markerKernel ρ) (markerQuadratic A B x))) /
    (1 + k ^ 2 * markerKernel ρ (markerQuadratic A B x) ^ 2 *
      (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2)) ^ 2 := by
  rw [surfaceGaussianCurvature_heightGraph (contDiff_markerBump A B k ρ),
    graphHessian_markerBump_det, graphAreaSq_markerBump]

/-- Identification with the true first/second fundamental-form Gaussian curvature,
including the support boundary where both kernel derivatives vanish. -/
theorem surfaceGaussianCurvature_markerBump (A B k : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : PolarPoint) :
    surfaceGaussianCurvature (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) x) x =
        markerCurvatureExpression A B k ρ x := by
  rw [surfaceGaussianCurvature_markerBump_kernel]
  dsimp only [markerCurvatureExpression]
  split_ifs with hx
  · have hs : markerQuadratic A B x < ρ ^ 2 := hx
    rw [deriv_markerKernel_of_lt hρ hs, markerKernel_eq_exp hρ hs]
    have he : Real.exp (-2 * (markerQuadratic A B x / (ρ ^ 2 - markerQuadratic A B x))) =
        Real.exp (-markerQuadratic A B x / (ρ ^ 2 - markerQuadratic A B x)) ^ 2 := by
      simp only [pow_two]
      rw [← Real.exp_add]
      congr 1
      ring
    change _ = A * B * k ^ 2 *
      Real.exp (-2 * (markerQuadratic A B x / (ρ ^ 2 - markerQuadratic A B x))) *
      (1 - 2 * markerQuadratic A B x * (ρ ^ 2 / (ρ ^ 2 - markerQuadratic A B x) ^ 2)) /
      (1 + k ^ 2 * Real.exp (-2 * (markerQuadratic A B x /
        (ρ ^ 2 - markerQuadratic A B x))) * (A ^ 2 * x.1 ^ 2 + B ^ 2 * x.2 ^ 2)) ^ 2
    rw [he]
    ring
  · have hs : ρ ^ 2 ≤ markerQuadratic A B x := le_of_not_gt hx
    rw [markerKernel_eq_zero hρ hs]
    ring

theorem surfaceGaussianCurvature_markerBump_zero (A B k : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    surfaceGaussianCurvature (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) 0) 0 = A * B * k ^ 2 := by
  rw [surfaceGaussianCurvature_markerBump A B k hρ, markerCurvatureExpression_zero A B k hρ]

theorem surfaceGaussianCurvature_markerBump_lt_peak {A B k ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hk : k ≠ 0) (hρ : ρ ≠ 0)
    {x : PolarPoint} (hx : x ≠ 0) :
    surfaceGaussianCurvature (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) x) x < A * B * k ^ 2 := by
  rw [surfaceGaussianCurvature_markerBump A B k hρ]
  exact markerCurvatureExpression_lt_peak hA hB hk hρ hx

theorem surfaceGaussianCurvature_markerBump_eq_peak_iff {A B k ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hk : k ≠ 0) (hρ : ρ ≠ 0) (x : PolarPoint) :
    surfaceGaussianCurvature (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) x) x = A * B * k ^ 2 ↔ x = 0 := by
  rw [surfaceGaussianCurvature_markerBump A B k hρ]
  exact markerCurvatureExpression_eq_peak_iff hA hB hk hρ x

theorem graphHessian_markerBump_zero (A B k ρ : ℝ) :
    graphHessian (markerBump A B k ρ) 0 = !![-k * A, 0; 0, -k * B] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphHessian_markerBump_apply, markerQuadratic]

theorem surfaceShapeMatrix_markerBump_zero (A B k ρ : ℝ) :
    surfaceShapeMatrix (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) 0) 0 = !![-k * A, 0; 0, -k * B] := by
  rw [surfaceShapeMatrix_heightGraph_critical (contDiff_markerBump A B k ρ)
    (fderiv_markerBump_zero A B k ρ), graphHessian_markerBump_zero]

/-- Distinct eigenvalues and their coordinate eigenvectors for the actual shape
matrix. Transport to tangent principal lines and cap assembly remain separate. -/
theorem surfaceShapeMatrix_markerBump_center_eigenvectors {A B k : ℝ} (ρ : ℝ)
    (hk : k ≠ 0) (hAB : A ≠ B) :
    (-k * A ≠ -k * B) ∧
    (surfaceShapeMatrix (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) 0) 0).mulVec ![1, 0] =
      (-k * A) • ![1, 0] ∧
    (surfaceShapeMatrix (graphMap id (markerBump A B k ρ))
      (graphUpwardNormal (markerBump A B k ρ) 0) 0).mulVec ![0, 1] =
      (-k * B) • ![0, 1] := by
  refine ⟨fun h => hAB (mul_left_cancel₀ (neg_ne_zero.mpr hk) h), ?_, ?_⟩
  all_goals
    rw [surfaceShapeMatrix_markerBump_zero]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end ContinuousFlexibility
