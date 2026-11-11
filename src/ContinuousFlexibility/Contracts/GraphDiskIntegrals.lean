import ContinuousFlexibility.Contracts.GraphFamilyCurvature
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Actual parameterized graph-disk integrals

The area density is the square root of the actual Gram determinant. The
mean-curvature integrand uses the actual shape operator and transported upward
normal. Identification with image-surface area, and with the outward normal
and integrals on the eventual closed sphere, remains a separate obligation.

The coordinate plane has its product norm; its rotations preserve Lebesgue
measure by their actual determinant, not by a false max-norm isometry claim.
-/

noncomputable section

namespace ContinuousFlexibility

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def surfaceParamAreaDensity (F : PolarPoint → E3) (x : PolarPoint) : ℝ :=
  Real.sqrt (surfaceGram F x).det

def cartesianCoordinateBasis : Module.Basis (Fin 2) ℝ PolarPoint :=
  Module.Basis.ofEquivFun (LinearEquiv.finTwoArrow ℝ ℝ).symm

theorem linearMap_det_eq_surfaceLinearMatrix (L : PolarPoint →L[ℝ] PolarPoint) :
    LinearMap.det L.toLinearMap = (surfaceLinearMatrix L).det := by
  rw [← LinearMap.det_toMatrix cartesianCoordinateBasis]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, cartesianCoordinateBasis, Module.Basis.coe_ofEquivFun,
      surfaceLinearMatrix, surfaceBasis]

theorem planarRotation_surfaceJacobian_det (t : ℝ) (x : PolarPoint) :
    (surfaceJacobian (planarRotation t) x).det = 1 := by
  unfold surfaceJacobian
  rw [(planarRotation t).hasFDerivAt.fderiv]
  simp only [surfaceLinearMatrix, planarRotation, planeRotationLinearMap_apply,
    surfaceBasis_zero, surfaceBasis_one, mul_one, mul_zero, sub_zero, zero_add,
    Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * t)]

theorem planarRotation_linearMap_det (t : ℝ) : LinearMap.det (planarRotation t).toLinearMap = 1 := by
  rw [linearMap_det_eq_surfaceLinearMatrix]
  simpa only [surfaceJacobian, (planarRotation t).hasFDerivAt.fderiv] using
    planarRotation_surfaceJacobian_det t 0

theorem measurePreserving_planarRotation (t : ℝ) :
    MeasurePreserving (planarRotation t) (volume : Measure PolarPoint) volume := by
  let : Measure.IsAddHaarMeasure (volume : Measure PolarPoint) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) volume
  refine ⟨(planarRotation t).continuous.measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure PolarPoint)
    (f := (planarRotation t).toLinearMap) (by rw [planarRotation_linearMap_det]; exact one_ne_zero)
  simpa only [ContinuousLinearMap.coe_coe, planarRotation_linearMap_det, inv_one,
    abs_one, ENNReal.ofReal_one, one_smul] using h

theorem integral_comp_planarRotation_closedDisk (t R : ℝ) (f : PolarPoint → ℝ) :
    (∫ x in {x : PolarPoint | cartesianRadius x ≤ R}, f (planarRotation t x)) =
      ∫ x in {x : PolarPoint | cartesianRadius x ≤ R}, f x := by
  have h := (measurePreserving_planarRotation t).restrict_image_emb
    (planarRotationHomeomorph t).toMeasurableEquiv.measurableEmbedding
    {x : PolarPoint | cartesianRadius x ≤ R}
  rw [planarRotation_image_closedCartesianDisk] at h
  exact h.integral_comp (planarRotationHomeomorph t).toMeasurableEquiv.measurableEmbedding f

theorem IsometricGraphDevelopment.surfaceGram_rotationFamily
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    surfaceGram (D.rotationFamily t) x = surfaceGram D.map x := by
  ext i j
  change inner ℝ (fderiv ℝ (D.rotationFamily t) x (surfaceBasis i))
    (fderiv ℝ (D.rotationFamily t) x (surfaceBasis j)) = _
  rw [D.rotationFamily_metric]
  exact (D.graph_metric x (surfaceBasis i) (surfaceBasis j)).symm

theorem IsometricGraphDevelopment.surfaceGram_comp_planarRotation
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    surfaceGram (D.map ∘ planarRotation t) x = surfaceGram D.map x := by
  have hd : DifferentiableAt ℝ D.map (planarRotation t x) :=
    D.smooth_graph.differentiable (by simp) _
  ext i j
  unfold surfaceGram surfaceFirstForm
  rw [fderiv_comp x hd (planarRotation t).differentiableAt,
    (planarRotation t).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change inner ℝ (fderiv ℝ (graphMap D.planar A.cartesianHeight) (planarRotation t x)
    (planarRotation t (surfaceBasis i)))
    (fderiv ℝ (graphMap D.planar A.cartesianHeight) (planarRotation t x)
      (planarRotation t (surfaceBasis j))) = _
  rw [D.graph_metric, cartesianMetric_planarRotation]
  exact (D.graph_metric x (surfaceBasis i) (surfaceBasis j)).symm

theorem IsometricGraphDevelopment.areaDensity_rotationFamily
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    surfaceParamAreaDensity (D.rotationFamily t) x = surfaceParamAreaDensity D.map x := by
  rw [surfaceParamAreaDensity, surfaceParamAreaDensity, D.surfaceGram_rotationFamily]

theorem IsometricGraphDevelopment.areaDensity_planarRotation
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    surfaceParamAreaDensity D.map (planarRotation t x) = surfaceParamAreaDensity D.map x := by
  have h := surfaceGram_det_comp
    (D.smooth_graph.differentiable (by simp) (planarRotation t x))
    (planarRotation t).differentiableAt
  change (surfaceGram (D.map ∘ planarRotation t) x).det =
    (surfaceJacobian (planarRotation t) x).det ^ 2 *
      (surfaceGram D.map (planarRotation t x)).det at h
  rw [D.surfaceGram_comp_planarRotation, planarRotation_surfaceJacobian_det, one_pow, one_mul] at h
  exact congrArg Real.sqrt h.symm

theorem continuous_surfaceParamAreaDensity {F : PolarPoint → E3}
    (hF : ContDiff ℝ ∞ F) : Continuous (surfaceParamAreaDensity F) := by
  have hd := hF.continuous_fderiv (by simp)
  have hg (i j : Fin 2) : Continuous (fun x => surfaceGram F x i j) :=
    (hd.clm_apply continuous_const).inner (hd.clm_apply continuous_const)
  have hdet : Continuous (fun x => (surfaceGram F x).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  exact hdet.sqrt

theorem continuous_heightGraph_meanCurvature {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) :
    Continuous (fun x => surfaceMeanCurvature (graphMap id z) (graphUpwardNormal z x) x) := by
  have hd := hz.continuous_fderiv (by simp)
  have hz' : ContDiff ℝ ∞ (fderiv ℝ z) := hz.fderiv_right (by simp)
  have hdd := hz'.continuous_fderiv (by simp)
  have hr : Continuous (radialPartial z) := hd.clm_apply continuous_const
  have ht : Continuous (angularPartial z) := hd.clm_apply continuous_const
  have hh (i j : Fin 2) : Continuous (fun x => graphHessian z x i j) :=
    (hdd.clm_apply continuous_const).clm_apply continuous_const
  have hsq : Continuous (graphAreaSq z) :=
    (continuous_const.add (hr.pow 2)).add (ht.pow 2)
  have hnum : Continuous (fun x =>
      (1 + angularPartial z x ^ 2) * graphHessian z x 0 0 -
        2 * radialPartial z x * angularPartial z x * graphHessian z x 0 1 +
        (1 + radialPartial z x ^ 2) * graphHessian z x 1 1) :=
    (((continuous_const.add (ht.pow 2)).mul (hh 0 0)).sub
      (((continuous_const.mul hr).mul ht).mul (hh 0 1))).add
        ((continuous_const.add (hr.pow 2)).mul (hh 1 1))
  have hc := hnum.div ((continuous_const.mul hsq).mul (contDiff_graphAreaDensity hz).continuous)
    (fun x => (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (graphAreaSq_pos z x))
      (graphAreaDensity_pos z x)).ne')
  have heq : (fun x => surfaceMeanCurvature (graphMap id z) (graphUpwardNormal z x) x) =
      fun x => ((1 + angularPartial z x ^ 2) * graphHessian z x 0 0 -
        2 * radialPartial z x * angularPartial z x * graphHessian z x 0 1 +
        (1 + radialPartial z x ^ 2) * graphHessian z x 1 1) /
      (2 * graphAreaSq z x * graphAreaDensity z x) :=
    funext (surfaceMeanCurvature_heightGraph hz)
  rw [heq]
  exact hc

theorem IsometricGraphDevelopment.continuous_upwardMeanCurvature
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    Continuous (fun x => surfaceMeanCurvature D.map (D.upwardGraphNormal x) x) := by
  have hc := (continuous_heightGraph_meanCurvature D.contDiff_physicalHeight).comp D.planar.continuous
  have heq : (fun x => surfaceMeanCurvature D.map (D.upwardGraphNormal x) x) =
      fun x => surfaceMeanCurvature (graphMap id D.physicalHeight)
        (graphUpwardNormal D.physicalHeight (D.planar x)) (D.planar x) :=
    funext D.meanCurvature_physical_graph
  rw [heq]
  exact hc

theorem IsometricGraphDevelopment.areaDensity_integrableOn_closedDisk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) :
    IntegrableOn (surfaceParamAreaDensity (D.rotationFamily t))
      {x : PolarPoint | cartesianRadius x ≤ R} volume :=
  (continuous_surfaceParamAreaDensity (D.rotationFamily_smooth t)).continuousOn.integrableOn_compact
    (isCompact_closedCartesianDisk R)

theorem IsometricGraphDevelopment.upwardMeanIntegrand_integrableOn_closedDisk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) :
    IntegrableOn (fun x => surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x *
      surfaceParamAreaDensity (D.rotationFamily t) x)
      {x : PolarPoint | cartesianRadius x ≤ R} volume := by
  have hh : Continuous (fun x => surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x) := by
    have heq : (fun x => surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x) =
        fun x => surfaceMeanCurvature D.map (D.upwardGraphNormal (planarRotation t x))
          (planarRotation t x) := funext (D.rotationFamily_meanCurvature t)
    rw [heq]
    exact D.continuous_upwardMeanCurvature.comp (planarRotation t).continuous
  exact (hh.mul (continuous_surfaceParamAreaDensity (D.rotationFamily_smooth t))).continuousOn.integrableOn_compact
    (isCompact_closedCartesianDisk R)

def IsometricGraphDevelopment.graphDiskArea
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) : ℝ :=
  ∫ x in {x : PolarPoint | cartesianRadius x ≤ R}, surfaceParamAreaDensity (D.rotationFamily t) x

def IsometricGraphDevelopment.graphDiskUpwardMeanIntegral
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) : ℝ :=
  ∫ x in {x : PolarPoint | cartesianRadius x ≤ R},
    surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x *
      surfaceParamAreaDensity (D.rotationFamily t) x

theorem IsometricGraphDevelopment.graphDiskArea_eq_zeroPhase
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) :
    D.graphDiskArea t R = D.graphDiskArea 0 R := by
  unfold IsometricGraphDevelopment.graphDiskArea
  congr 1
  funext x
  rw [D.areaDensity_rotationFamily, D.areaDensity_rotationFamily]

theorem IsometricGraphDevelopment.graphDiskUpwardMeanIntegral_eq_zeroPhase
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t R : ℝ) :
    D.graphDiskUpwardMeanIntegral t R = D.graphDiskUpwardMeanIntegral 0 R := by
  have heq : (fun x => surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x *
      surfaceParamAreaDensity (D.rotationFamily t) x) =
      fun x => surfaceMeanCurvature D.map (D.upwardGraphNormal (planarRotation t x))
        (planarRotation t x) * surfaceParamAreaDensity D.map (planarRotation t x) := by
    funext x
    rw [D.rotationFamily_meanCurvature, D.areaDensity_rotationFamily, D.areaDensity_planarRotation]
  unfold IsometricGraphDevelopment.graphDiskUpwardMeanIntegral
  rw [heq]
  rw [integral_comp_planarRotation_closedDisk t R
    (fun x => surfaceMeanCurvature D.map (D.upwardGraphNormal x) x *
      surfaceParamAreaDensity D.map x)]
  congr 1
  funext x
  have h0 : D.rotationFamily 0 = D.map := funext D.rotationFamily_zero
  simp only [h0, IsometricGraphDevelopment.rotationNormal_zero]

end ContinuousFlexibility
