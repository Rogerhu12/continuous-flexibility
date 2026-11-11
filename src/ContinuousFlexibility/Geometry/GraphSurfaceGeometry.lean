import ContinuousFlexibility.Geometry.GraphEmbedding
import ContinuousFlexibility.Geometry.SurfaceGeometry
import ContinuousFlexibility.Scalar.HeightDerivatives

/-!
# Differential geometry of actual height graphs

The tangent vectors and normal below use the actual Fréchet derivative of
`graphMap id z`. All inner products are those of the Euclidean target `E3`;
the product norm on the coordinate plane is not used as a Euclidean metric.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The positive square of the area density of a height graph. -/
def graphAreaSq (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  1 + radialPartial z x ^ 2 + angularPartial z x ^ 2

/-- The area density of a height graph in Cartesian coordinates. -/
def graphAreaDensity (z : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  Real.sqrt (graphAreaSq z x)

/-- The normal pointing towards positive third coordinate. -/
def graphUpwardNormal (z : PolarPoint → ℝ) (x : PolarPoint) : E3 :=
  (graphAreaDensity z x)⁻¹ •
    graphMap id (fun _ => 1) (-radialPartial z x, -angularPartial z x)

theorem graphAreaSq_pos (z : PolarPoint → ℝ) (x : PolarPoint) :
    0 < graphAreaSq z x := by
  unfold graphAreaSq
  positivity

theorem graphAreaDensity_pos (z : PolarPoint → ℝ) (x : PolarPoint) :
    0 < graphAreaDensity z x := Real.sqrt_pos.2 (graphAreaSq_pos z x)

theorem graphAreaDensity_sq (z : PolarPoint → ℝ) (x : PolarPoint) :
    graphAreaDensity z x ^ 2 = graphAreaSq z x :=
  Real.sq_sqrt (graphAreaSq_pos z x).le

@[simp] theorem graphUpwardNormal_zero (z : PolarPoint → ℝ) (x : PolarPoint) :
    graphUpwardNormal z x 0 = -radialPartial z x / graphAreaDensity z x := by
  simp [graphUpwardNormal, div_eq_mul_inv, mul_comm]

@[simp] theorem graphUpwardNormal_one (z : PolarPoint → ℝ) (x : PolarPoint) :
    graphUpwardNormal z x 1 = -angularPartial z x / graphAreaDensity z x := by
  simp [graphUpwardNormal, div_eq_mul_inv, mul_comm]

@[simp] theorem graphUpwardNormal_two (z : PolarPoint → ℝ) (x : PolarPoint) :
    graphUpwardNormal z x 2 = 1 / graphAreaDensity z x := by
  simp [graphUpwardNormal]

theorem graphUpwardNormal_inner_self (z : PolarPoint → ℝ) (x : PolarPoint) :
    inner ℝ (graphUpwardNormal z x) (graphUpwardNormal z x) = 1 := by
  rw [e3_inner_coordinates]
  simp only [graphUpwardNormal_zero, graphUpwardNormal_one, graphUpwardNormal_two]
  have hd := (ne_of_gt (graphAreaDensity_pos z x))
  have hs := graphAreaDensity_sq z x
  unfold graphAreaSq at hs
  field_simp
  nlinarith

theorem graphUpwardNormal_norm (z : PolarPoint → ℝ) (x : PolarPoint) :
    ‖graphUpwardNormal z x‖ = 1 := by
  have h := graphUpwardNormal_inner_self z x
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (graphUpwardNormal z x)]

theorem height_fderiv_coordinates (z : PolarPoint → ℝ) (x v : PolarPoint) :
    fderiv ℝ z x v = radialPartial z x * v.1 + angularPartial z x * v.2 := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]
  simp only [smul_eq_mul, radialPartial, angularPartial]
  ring

theorem graphUpwardNormal_orthogonal {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) (v : PolarPoint) :
    inner ℝ (fderiv ℝ (graphMap id z) x v) (graphUpwardNormal z x) = 0 := by
  rw [fderiv_graphMap differentiableAt_id hz, e3_inner_coordinates]
  simp only [graphDifferential_apply_zero, graphDifferential_apply_one,
    graphDifferential_apply_two, fderiv_id, ContinuousLinearMap.id_apply,
    graphUpwardNormal_zero, graphUpwardNormal_one, graphUpwardNormal_two]
  rw [height_fderiv_coordinates]
  ring

theorem inner_heightGraph_fderiv {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) (u v : PolarPoint) :
    inner ℝ (fderiv ℝ (graphMap id z) x u) (fderiv ℝ (graphMap id z) x v) =
      coordinateEuclideanPair u v + fderiv ℝ z x u * fderiv ℝ z x v := by
  rw [fderiv_graphMap differentiableAt_id hz, inner_graphDifferential]
  simp

theorem heightGraph_fderiv_injective {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) :
    Function.Injective (fderiv ℝ (graphMap id z) x) := by
  apply graphMap_fderiv_injective_of_planar differentiableAt_id hz
  simpa using Function.injective_id

/-- The second derivative of a height graph has only a vertical component. -/
theorem heightGraph_second_fderiv {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (x u v : PolarPoint) :
    fderiv ℝ (fderiv ℝ (graphMap id z)) x u v =
      (fderiv ℝ (fderiv ℝ z) x u v) • e3Basis 2 := by
  have hF : ContDiff ℝ ∞ (graphMap id z) := contDiff_graphMap contDiff_id hz
  have hFd : DifferentiableAt ℝ (fderiv ℝ (graphMap id z)) x :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hzd : DifferentiableAt ℝ (fderiv ℝ z) x :=
    (hz.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have heval : (fun y => fderiv ℝ (graphMap id z) y v) =
      graphMap (fun _ => v) (fun y => fderiv ℝ z y v) := by
    funext y
    rw [fderiv_graphMap differentiableAt_id (hz.differentiable (by simp) y)]
    ext i
    fin_cases i <;> simp
  have hd := congrArg (fun f : PolarPoint → E3 => fderiv ℝ f x u) heval
  rw [fderiv_clm_apply hFd (differentiableAt_const v)] at hd
  simp only [fderiv_fun_const,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hd
  rw [fderiv_graphMap (differentiableAt_const v)
    (hzd.clm_apply (differentiableAt_const v))] at hd
  rw [fderiv_fun_const, fderiv_clm_apply hzd (differentiableAt_const v)] at hd
  simpa [graphDifferential] using hd

theorem graphUpwardNormal_isUnitSurfaceNormal {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) :
    IsUnitSurfaceNormal (graphMap id z) x (graphUpwardNormal z x) :=
  ⟨graphUpwardNormal_norm z x, graphUpwardNormal_orthogonal hz⟩

theorem contDiff_graphAreaDensity {z : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (graphAreaDensity z) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ z) := hz.fderiv_right (by simp)
  have hr : ContDiff ℝ ∞ (radialPartial z) := hd.clm_apply contDiff_const
  have ha : ContDiff ℝ ∞ (angularPartial z) := hd.clm_apply contDiff_const
  exact ((contDiff_const.add (hr.pow 2)).add (ha.pow 2)).sqrt
    (fun x => ne_of_gt (graphAreaSq_pos z x))

theorem contDiff_graphUpwardNormal {z : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (graphUpwardNormal z) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ z) := hz.fderiv_right (by simp)
  have hr : ContDiff ℝ ∞ (radialPartial z) := hd.clm_apply contDiff_const
  have ha : ContDiff ℝ ∞ (angularPartial z) := hd.clm_apply contDiff_const
  exact ((contDiff_graphAreaDensity hz).inv (fun x => ne_of_gt (graphAreaDensity_pos z x))).smul
    (contDiff_graphMap contDiff_id contDiff_const |>.comp (hr.neg.prodMk ha.neg))

theorem surfaceGram_heightGraph {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) :
    surfaceGram (graphMap id z) x =
      !![1 + radialPartial z x ^ 2, radialPartial z x * angularPartial z x;
         radialPartial z x * angularPartial z x, 1 + angularPartial z x ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [surfaceGram, surfaceFirstForm]
    rw [inner_heightGraph_fderiv hz]
    simp [coordinateEuclideanPair, radialPartial, angularPartial, pow_two, mul_comm]

/-- The proposed graph density is the square root of the actual induced Gram determinant. -/
theorem surfaceGram_heightGraph_det {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) :
    (surfaceGram (graphMap id z) x).det = graphAreaSq z x := by
  rw [surfaceGram_heightGraph hz, Matrix.det_fin_two]
  simp [graphAreaSq]
  ring

theorem graphAreaDensity_eq_sqrt_gram_det {z : PolarPoint → ℝ} {x : PolarPoint}
    (hz : DifferentiableAt ℝ z x) :
    graphAreaDensity z x = Real.sqrt (surfaceGram (graphMap id z) x).det := by
  rw [surfaceGram_heightGraph_det hz]
  rfl

theorem surfaceSecondForm_heightGraph {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (x u v : PolarPoint) :
    surfaceSecondForm (graphMap id z) (graphUpwardNormal z x) x u v =
      fderiv ℝ (fderiv ℝ z) x u v / graphAreaDensity z x := by
  rw [surfaceSecondForm, heightGraph_second_fderiv hz, e3_inner_coordinates]
  simp [e3Basis, div_eq_mul_inv]

/-- The coordinate matrix of the actual second derivative of the height. -/
def graphHessian (z : PolarPoint → ℝ) (x : PolarPoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ z) x (surfaceBasis i) (surfaceBasis j)

theorem graphHessian_symm {z : PolarPoint → ℝ} (hz : ContDiff ℝ ∞ z)
    (x : PolarPoint) (i j : Fin 2) : graphHessian z x i j = graphHessian z x j i :=
  hz.contDiffAt.isSymmSndFDerivAt (by simp) _ _

theorem surfaceSecondMatrix_heightGraph {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (x : PolarPoint) :
    surfaceSecondMatrix (graphMap id z) (graphUpwardNormal z x) x =
      (graphAreaDensity z x)⁻¹ • graphHessian z x := by
  ext i j
  simp [surfaceSecondMatrix, surfaceSecondForm_heightGraph hz, graphHessian,
    div_eq_mul_inv, mul_comm]

/-- Gaussian curvature identified from the actual first and second fundamental forms. -/
theorem surfaceGaussianCurvature_heightGraph {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (x : PolarPoint) :
    surfaceGaussianCurvature (graphMap id z) (graphUpwardNormal z x) x =
      (graphHessian z x).det / graphAreaSq z x ^ 2 := by
  rw [surfaceGaussianCurvature, surfaceShapeMatrix, Matrix.det_mul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
    surfaceGram_heightGraph_det (hz.differentiable (by simp) x),
    surfaceSecondMatrix_heightGraph hz]
  simp only [Matrix.det_smul, Fintype.card_fin]
  have hd := ne_of_gt (graphAreaDensity_pos z x)
  have hq := ne_of_gt (graphAreaSq_pos z x)
  have hs := graphAreaDensity_sq z x
  field_simp
  rw [hs]

theorem surfaceGaussianCurvature_heightGraph_coordinates {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (x : PolarPoint) :
    surfaceGaussianCurvature (graphMap id z) (graphUpwardNormal z x) x =
      (graphHessian z x 0 0 * graphHessian z x 1 1 - graphHessian z x 0 1 ^ 2) /
        graphAreaSq z x ^ 2 := by
  rw [surfaceGaussianCurvature_heightGraph hz, Matrix.det_fin_two,
    graphHessian_symm hz x 1 0]
  simp only [pow_two]

/-- The signed mean curvature, with the upward unit normal and convention `tr(S)/2`. -/
theorem surfaceMeanCurvature_heightGraph {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) (x : PolarPoint) :
    surfaceMeanCurvature (graphMap id z) (graphUpwardNormal z x) x =
      ((1 + angularPartial z x ^ 2) * graphHessian z x 0 0 -
        2 * radialPartial z x * angularPartial z x * graphHessian z x 0 1 +
        (1 + radialPartial z x ^ 2) * graphHessian z x 1 1) /
      (2 * graphAreaSq z x * graphAreaDensity z x) := by
  rw [surfaceMeanCurvature, surfaceShapeMatrix, Matrix.inv_def,
    surfaceGram_heightGraph_det (hz.differentiable (by simp) x),
    surfaceGram_heightGraph (hz.differentiable (by simp) x),
    Matrix.adjugate_fin_two, surfaceSecondMatrix_heightGraph hz,
    Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul, Ring.inverse_eq_inv, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [graphHessian_symm hz x 1 0]
  ring

theorem surfaceShapeMatrix_heightGraph_critical {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) {x : PolarPoint} (hc : fderiv ℝ z x = 0) :
    surfaceShapeMatrix (graphMap id z) (graphUpwardNormal z x) x = graphHessian z x := by
  have hr : radialPartial z x = 0 := by simp [radialPartial, hc]
  have ha : angularPartial z x = 0 := by simp [angularPartial, hc]
  have hg : surfaceGram (graphMap id z) x = 1 := by
    rw [surfaceGram_heightGraph (hz.differentiable (by simp) x), hr, ha]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hd : graphAreaDensity z x = 1 := by simp [graphAreaDensity, graphAreaSq, hr, ha]
  rw [surfaceShapeMatrix, hg, surfaceSecondMatrix_heightGraph hz, hd]
  simp

end ContinuousFlexibility
