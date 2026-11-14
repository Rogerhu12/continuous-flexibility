module

public import ContinuousFlexibility.Contracts.GraphDiskIntegrals

/-!
# A genuine uniform curvature bound for the whole graph phase family

Both curvatures are computed from the actual shape matrix and constructed unit
normal. Compactness bounds the fixed physical graph; proved rotation naturality
then bounds every real phase by the same constant. No curvature bound is an
input, and no marked cap or analytic core existence is asserted here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem continuous_heightGraph_gaussianCurvature {z : PolarPoint → ℝ}
    (hz : ContDiff ℝ ∞ z) :
    Continuous (fun x => surfaceGaussianCurvature (graphMap id z) (graphUpwardNormal z x) x) := by
  have hd := hz.continuous_fderiv (by simp)
  have hz' : ContDiff ℝ ∞ (fderiv ℝ z) := hz.fderiv_right (by simp)
  have hdd := hz'.continuous_fderiv (by simp)
  have hr : Continuous (radialPartial z) := hd.clm_apply continuous_const
  have ht : Continuous (angularPartial z) := hd.clm_apply continuous_const
  have hh (i j : Fin 2) : Continuous (fun x => graphHessian z x i j) :=
    (hdd.clm_apply continuous_const).clm_apply continuous_const
  have hsq : Continuous (graphAreaSq z) :=
    (continuous_const.add (hr.pow 2)).add (ht.pow 2)
  have hn : Continuous (fun x => (graphHessian z x).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hh 0 0).mul (hh 1 1)).sub ((hh 0 1).mul (hh 1 0))
  have hquot := hn.div (hsq.pow 2) (fun x => pow_ne_zero 2 (graphAreaSq_pos z x).ne')
  have heq : (fun x => surfaceGaussianCurvature (graphMap id z) (graphUpwardNormal z x) x) =
      fun x => (graphHessian z x).det / graphAreaSq z x ^ 2 :=
    funext (surfaceGaussianCurvature_heightGraph hz)
  rw [heq]
  exact hquot

theorem IsometricGraphDevelopment.continuous_upwardGaussianCurvature
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    Continuous (fun x => surfaceGaussianCurvature D.map (D.upwardGraphNormal x) x) := by
  have hc := (continuous_heightGraph_gaussianCurvature D.contDiff_physicalHeight).comp D.planar.continuous
  have heq : (fun x => surfaceGaussianCurvature D.map (D.upwardGraphNormal x) x) =
      fun x => surfaceGaussianCurvature (graphMap id D.physicalHeight)
        (graphUpwardNormal D.physicalHeight (D.planar x)) (D.planar x) :=
    funext D.gaussianCurvature_physical_graph
  rw [heq]
  exact hc

theorem IsometricGraphDevelopment.exists_rotationFamily_curvature_bounds
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∀ x : PolarPoint, cartesianRadius x ≤ R →
      |surfaceGaussianCurvature (D.rotationFamily t) (D.rotationNormal t x) x| ≤ C ∧
      |surfaceMeanCurvature (D.rotationFamily t) (D.rotationNormal t x) x| ≤ C := by
  obtain ⟨CK, hK⟩ := (isCompact_closedCartesianDisk R).bddAbove_image
    D.continuous_upwardGaussianCurvature.abs.continuousOn
  obtain ⟨CH, hH⟩ := (isCompact_closedCartesianDisk R).bddAbove_image
    D.continuous_upwardMeanCurvature.abs.continuousOn
  refine ⟨max (max CK CH) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t x hx => ?_⟩
  have hxr : planarRotation t x ∈ {y : PolarPoint | cartesianRadius y ≤ R} := by simpa using hx
  rw [D.rotationFamily_gaussianCurvature, D.rotationFamily_meanCurvature]
  exact ⟨(hK ⟨planarRotation t x, hxr, rfl⟩).trans
      ((le_max_left CK CH).trans (le_max_left _ _)),
    (hH ⟨planarRotation t x, hxr, rfl⟩).trans
      ((le_max_right CK CH).trans (le_max_left _ _))⟩

end ContinuousFlexibility
