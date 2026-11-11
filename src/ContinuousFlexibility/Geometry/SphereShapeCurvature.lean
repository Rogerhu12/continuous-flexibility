import ContinuousFlexibility.Geometry.SphereShapeOperator
import ContinuousFlexibility.Geometry.SphereCurvature
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Identifying the actual tangent shape operator with coordinate curvature

The coordinate matrix is identified by its genuine Weingarten equation.
A chart differential then conjugates the actual sphere tangent operator to
that matrix, so its trace and determinant are the existing coordinate mean
and Gaussian curvatures. The same normal is used throughout.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Manifold Topology BigOperators

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}
local notation "TSphere" => (fun x : SpherePoint => TangentSpace (𝓡 2) x)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

set_option backward.isDefEq.respectTransparency false

private def shapeCoordinateBasis : Module.Basis (Fin 2) ℝ PolarPoint :=
  Module.Basis.finTwoProd ℝ

private theorem shapeCoordinateBasis_eq (i : Fin 2) :
    shapeCoordinateBasis i = surfaceBasis i := by
  fin_cases i <;> simp [shapeCoordinateBasis]

/-- The genuine Weingarten equation determines the already defined coordinate
shape matrix, using the actual first and second derivatives. -/
theorem surfaceShapeMatrix_eq_matrix_of_weingarten
    {F N : PolarPoint → E3} {x : PolarPoint}
    (hF : ContDiff ℝ ∞ F) (hN : DifferentiableAt ℝ N x)
    (hi : Function.Injective (fderiv ℝ F x))
    (ho : ∀ y v, inner ℝ (fderiv ℝ F y v) (N y) = 0)
    (S : PolarPoint →ₗ[ℝ] PolarPoint)
    (hW : ∀ v, fderiv ℝ F x (S v) = -fderiv ℝ N x v) :
    LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) S =
      surfaceShapeMatrix F (N x) x := by
  let b := shapeCoordinateBasis
  let M := LinearMap.toMatrix b b S
  change M = surfaceShapeMatrix F (N x) x
  apply surfaceShapeMatrix_unique hi (N x)
  have hcol (j : Fin 2) :
      (∑ i : Fin 2, M i j • fderiv ℝ F x (b i)) =
        fderiv ℝ F x (S (b j)) := by
    simpa only [M, LinearMap.toMatrix_apply, map_sum, map_smul] using
      congrArg (fderiv ℝ F x) (b.sum_repr (S (b j)))
  ext i j
  change (∑ l : Fin 2,
      surfaceFirstForm F x (surfaceBasis i) (surfaceBasis l) * M l j) =
    surfaceSecondForm F (N x) x (surfaceBasis i) (surfaceBasis j)
  simp_rw [← shapeCoordinateBasis_eq]
  change (∑ l : Fin 2, surfaceFirstForm F x (b i) (b l) * M l j) =
    surfaceSecondForm F (N x) x (b i) (b j)
  calc
    (∑ l : Fin 2, surfaceFirstForm F x (b i) (b l) * M l j) =
        inner ℝ (fderiv ℝ F x (b i)) (fderiv ℝ F x (S (b j))) := by
      rw [← hcol j]
      simp only [surfaceFirstForm, inner_sum, inner_smul_right, mul_comm]
    _ = -inner ℝ (fderiv ℝ F x (b i)) (fderiv ℝ N x (b j)) := by
      rw [hW, inner_neg_right]
    _ = surfaceSecondForm F (N x) x (b j) (b i) :=
      (surfaceSecondForm_eq_neg_normal_derivative hF hN ho (b j) (b i)).symm
    _ = surfaceSecondForm F (N x) x (b i) (b j) :=
      surfaceSecondForm_symm hF (N x) x (b j) (b i)

theorem surfaceMeanCurvature_eq_trace_of_weingarten
    {F N : PolarPoint → E3} {x : PolarPoint}
    (hF : ContDiff ℝ ∞ F) (hN : DifferentiableAt ℝ N x)
    (hi : Function.Injective (fderiv ℝ F x))
    (ho : ∀ y v, inner ℝ (fderiv ℝ F y v) (N y) = 0)
    (S : PolarPoint →ₗ[ℝ] PolarPoint)
    (hW : ∀ v, fderiv ℝ F x (S v) = -fderiv ℝ N x v) :
    surfaceMeanCurvature F (N x) x = LinearMap.trace ℝ PolarPoint S / 2 := by
  rw [surfaceMeanCurvature,
    ← surfaceShapeMatrix_eq_matrix_of_weingarten hF hN hi ho S hW,
    ← LinearMap.trace_eq_matrix_trace ℝ (Module.Basis.finTwoProd ℝ) S]

theorem surfaceGaussianCurvature_eq_det_of_weingarten
    {F N : PolarPoint → E3} {x : PolarPoint}
    (hF : ContDiff ℝ ∞ F) (hN : DifferentiableAt ℝ N x)
    (hi : Function.Injective (fderiv ℝ F x))
    (ho : ∀ y v, inner ℝ (fderiv ℝ F y v) (N y) = 0)
    (S : PolarPoint →ₗ[ℝ] PolarPoint)
    (hW : ∀ v, fderiv ℝ F x (S v) = -fderiv ℝ N x v) :
    surfaceGaussianCurvature F (N x) x = LinearMap.det S := by
  rw [surfaceGaussianCurvature,
    ← surfaceShapeMatrix_eq_matrix_of_weingarten hF hN hi ho S hW]
  exact LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ) S

/-- The genuine chart differential, with the canonical source tangent
identification removed. Its target remains the actual sphere tangent fiber. -/
def sphereParametricDifferential (P : PolarPoint → SpherePoint) (y : PolarPoint) :
    PolarPoint →L[ℝ] TSphere (P y) :=
  (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y).comp
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm :
      PolarPoint →L[ℝ] TangentSpace 𝓘(ℝ, PolarPoint) y)

theorem sphere_fderiv_comp_param {G : SpherePoint → E3} {P : PolarPoint → SpherePoint}
    (hG : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ G)
    (hP : ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ P) (y : PolarPoint) :
    fderiv ℝ (G ∘ P) y =
      (mvfderiv (𝓡 2) G (P y)).comp (sphereParametricDifferential P y) := by
  have hh := mvfderiv_comp y ((hG (P y)).mdifferentiableAt (by simp))
    ((hP y).mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv] at hh
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg
    (fun L => L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm z)) hh
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,
    sphereParametricDifferential] using hz

/-- A full-rank chart gives a genuine continuous linear equivalence onto the
actual tangent space. No extra norm on that tangent space is used. -/
def sphereParametricTangentEquiv (P : PolarPoint → SpherePoint) (y : PolarPoint)
    (hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y)) :
    PolarPoint ≃L[ℝ] TSphere (P y) :=
  (LinearEquiv.ofBijective (sphereParametricDifferential P y).toLinearMap
    (hPi.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.bijective)).toContinuousLinearEquiv

theorem sphereParametricTangentEquiv_toContinuousLinearMap
    (P : PolarPoint → SpherePoint) (y : PolarPoint)
    (hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y)) :
    (sphereParametricTangentEquiv P y hPi : PolarPoint →L[ℝ] TSphere (P y)) =
      sphereParametricDifferential P y := by
  apply ContinuousLinearMap.ext
  intro z
  rfl

/-- The actual tangent-space operator, conjugated by the actual chart
differential, has exactly the existing coordinate shape matrix. -/
theorem sphereShapeOperator_matrix_in_chart {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    {P : PolarPoint → SpherePoint}
    (hP : ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ P) (y : PolarPoint)
    (hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y)) :
    LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      ((sphereParametricTangentEquiv P y hPi).toLinearEquiv.symm.conj
        (sphereShapeOperator F N (P y)).toLinearMap) =
      surfaceShapeMatrix (F ∘ P) (N (P y)) y := by
  let e := sphereParametricTangentEquiv P y hPi
  let S := e.toLinearEquiv.symm.conj (sphereShapeOperator F N (P y)).toLinearMap
  have he : (e : PolarPoint →L[ℝ] TSphere (P y)) = sphereParametricDifferential P y :=
    sphereParametricTangentEquiv_toContinuousLinearMap P y hPi
  have hFc : ContDiff ℝ ∞ (F ∘ P) := (hF.comp hP).contDiff
  have hNc : ContDiff ℝ ∞ (N ∘ P) := (hN.comp hP).contDiff
  have hdc : Function.Injective (fderiv ℝ (F ∘ P) y) := by
    rw [sphere_fderiv_comp_param hF hP y, ← he]
    exact ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (P y))).injective.comp
      (hi (P y))).comp e.injective
  have hoc : ∀ z v, inner ℝ (fderiv ℝ (F ∘ P) z v) ((N ∘ P) z) = 0 := by
    intro z v
    rw [sphere_fderiv_comp_param hF hP z]
    exact ho (P z) (sphereParametricDifferential P z v)
  apply surfaceShapeMatrix_eq_matrix_of_weingarten hFc
    (hNc.differentiable (by simp) y) hdc hoc S
  intro v
  rw [sphere_fderiv_comp_param hF hP y, sphere_fderiv_comp_param hN hP y, ← he]
  change mvfderiv (𝓡 2) F (P y) (e (S v)) = -mvfderiv (𝓡 2) N (P y) (e v)
  change mvfderiv (𝓡 2) F (P y)
      (e (e.symm (sphereShapeOperator F N (P y) (e v)))) = _
  rw [e.apply_symm_apply]
  exact sphereShapeOperator_weingarten hN hi hu ho (P y) (e v)

/-- The signed mean curvature computed in a genuine chart equals half the
trace of the actual tangent-space shape operator. -/
theorem sphereShapeOperator_trace_in_chart {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    {P : PolarPoint → SpherePoint}
    (hP : ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ P) (y : PolarPoint)
    (hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y)) :
    LinearMap.trace ℝ (TSphere (P y)) (sphereShapeOperator F N (P y)).toLinearMap / 2 =
      surfaceMeanCurvature (F ∘ P) (N (P y)) y := by
  let e := sphereParametricTangentEquiv P y hPi
  let S := e.toLinearEquiv.symm.conj (sphereShapeOperator F N (P y)).toLinearMap
  have hM : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) S =
      surfaceShapeMatrix (F ∘ P) (N (P y)) y :=
    sphereShapeOperator_matrix_in_chart hF hN hi hu ho hP y hPi
  calc
    LinearMap.trace ℝ (TSphere (P y)) (sphereShapeOperator F N (P y)).toLinearMap / 2 =
        LinearMap.trace ℝ PolarPoint S / 2 := by
      symm
      exact congrArg (fun r : ℝ => r / 2)
        (LinearMap.trace_conj' (sphereShapeOperator F N (P y)).toLinearMap e.toLinearEquiv.symm)
    _ = (LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) S).trace / 2 :=
      congrArg (fun r : ℝ => r / 2)
        (LinearMap.trace_eq_matrix_trace ℝ (Module.Basis.finTwoProd ℝ) S)
    _ = surfaceMeanCurvature (F ∘ P) (N (P y)) y := by
      change _ = (surfaceShapeMatrix (F ∘ P) (N (P y)) y).trace / 2
      rw [hM]

/-- Gaussian curvature computed in a genuine chart is the determinant of
the same actual tangent-space operator. -/
theorem sphereShapeOperator_det_in_chart {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    {P : PolarPoint → SpherePoint}
    (hP : ContMDiff 𝓘(ℝ, PolarPoint) (𝓡 2) ∞ P) (y : PolarPoint)
    (hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2) P y)) :
    LinearMap.det (sphereShapeOperator F N (P y)).toLinearMap =
      surfaceGaussianCurvature (F ∘ P) (N (P y)) y := by
  let e := sphereParametricTangentEquiv P y hPi
  let S := e.toLinearEquiv.symm.conj (sphereShapeOperator F N (P y)).toLinearMap
  have hM : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) S =
      surfaceShapeMatrix (F ∘ P) (N (P y)) y :=
    sphereShapeOperator_matrix_in_chart hF hN hi hu ho hP y hPi
  calc
    LinearMap.det (sphereShapeOperator F N (P y)).toLinearMap = LinearMap.det S := by
      symm
      simpa only [S, LinearEquiv.conj_apply, LinearMap.comp_assoc] using
        (LinearMap.det_conj (sphereShapeOperator F N (P y)).toLinearMap e.toLinearEquiv.symm)
    _ = (LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) S).det :=
      (LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ) S).symm
    _ = surfaceGaussianCurvature (F ∘ P) (N (P y)) y := by
      change _ = (surfaceShapeMatrix (F ∘ P) (N (P y)) y).det
      rw [hM]

/-- Signed mean curvature of the actual sphere immersion, defined by the
trace of its genuine tangent-space shape operator. -/
def sphereMeanCurvature (F N : SpherePoint → E3) (x : SpherePoint) : ℝ :=
  LinearMap.trace ℝ (TSphere x) (sphereShapeOperator F N x).toLinearMap / 2

theorem contMDiff_sphereMeanCurvature {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (sphereMeanCurvature F N) :=
  sphereShapeOperator_trace_contMDiff hF hN hi hu ho

theorem sphereMeanCurvature_north {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    sphereMeanCurvature F N x =
      surfaceMeanCurvature (sphereNorthSurfaceChart F) (N x) (sphereNorthChart x) := by
  have hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2)
      sphereNorthInverse (sphereNorthChart x)) :=
    mdifferentiable_sphereNorthCoordinates.symm.mfderiv_bijective (Set.mem_univ _)
  let B : SpherePoint → Prop := fun z =>
    sphereMeanCurvature F N z =
      surfaceMeanCurvature (sphereNorthSurfaceChart F) (N z) (sphereNorthChart x)
  have hc : B (sphereNorthInverse (sphereNorthChart x)) :=
    sphereShapeOperator_trace_in_chart hF hN hi hu ho
      contMDiff_sphereNorthInverse (sphereNorthChart x) hPi
  exact Eq.mp (congrArg B (sphereNorthInverse_chart x hx)) hc

theorem sphereMeanCurvature_south {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    sphereMeanCurvature F N x =
      surfaceMeanCurvature (sphereSouthSurfaceChart F) (N x) (sphereSouthChart x) := by
  have hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2)
      sphereSouthInverse (sphereSouthChart x)) :=
    mdifferentiable_sphereSouthCoordinates.symm.mfderiv_bijective (Set.mem_univ _)
  let B : SpherePoint → Prop := fun z =>
    sphereMeanCurvature F N z =
      surfaceMeanCurvature (sphereSouthSurfaceChart F) (N z) (sphereSouthChart x)
  have hc : B (sphereSouthInverse (sphereSouthChart x)) :=
    sphereShapeOperator_trace_in_chart hF hN hi hu ho
      contMDiff_sphereSouthInverse (sphereSouthChart x) hPi
  exact Eq.mp (congrArg B (sphereSouthInverse_chart x hx)) hc

theorem sphereShapeOperator_det_north {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (hx : x ∈ sphereNorthSource) :
    LinearMap.det (sphereShapeOperator F N x).toLinearMap =
      surfaceGaussianCurvature (sphereNorthSurfaceChart F) (N x) (sphereNorthChart x) := by
  have hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2)
      sphereNorthInverse (sphereNorthChart x)) :=
    mdifferentiable_sphereNorthCoordinates.symm.mfderiv_bijective (Set.mem_univ _)
  let B : SpherePoint → Prop := fun z =>
    LinearMap.det (sphereShapeOperator F N z).toLinearMap =
      surfaceGaussianCurvature (sphereNorthSurfaceChart F) (N z) (sphereNorthChart x)
  have hc : B (sphereNorthInverse (sphereNorthChart x)) :=
    sphereShapeOperator_det_in_chart hF hN hi hu ho
      contMDiff_sphereNorthInverse (sphereNorthChart x) hPi
  exact Eq.mp (congrArg B (sphereNorthInverse_chart x hx)) hc

theorem sphereShapeOperator_det_south {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (x : SpherePoint) (hx : x ∈ sphereSouthSource) :
    LinearMap.det (sphereShapeOperator F N x).toLinearMap =
      surfaceGaussianCurvature (sphereSouthSurfaceChart F) (N x) (sphereSouthChart x) := by
  have hPi : Function.Bijective (mfderiv 𝓘(ℝ, PolarPoint) (𝓡 2)
      sphereSouthInverse (sphereSouthChart x)) :=
    mdifferentiable_sphereSouthCoordinates.symm.mfderiv_bijective (Set.mem_univ _)
  let B : SpherePoint → Prop := fun z =>
    LinearMap.det (sphereShapeOperator F N z).toLinearMap =
      surfaceGaussianCurvature (sphereSouthSurfaceChart F) (N z) (sphereSouthChart x)
  have hc : B (sphereSouthInverse (sphereSouthChart x)) :=
    sphereShapeOperator_det_in_chart hF hN hi hu ho
      contMDiff_sphereSouthInverse (sphereSouthChart x) hPi
  exact Eq.mp (congrArg B (sphereSouthInverse_chart x hx)) hc

/-- The existing global chart-defined Gaussian curvature is the determinant
of the actual tangent operator, in both charts and across the equator. -/
theorem sphereShapeOperator_det_eq_gaussian {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) (x : SpherePoint) :
    LinearMap.det (sphereShapeOperator F N x).toLinearMap = sphereGaussianCurvature F N x := by
  by_cases hx : 0 ≤ (x : E3) 2
  · have hn : x ∈ sphereNorthSource := by change (x : E3) 2 ≠ -1; linarith
    simpa only [sphereGaussianCurvature, hx, ↓reduceIte] using
      sphereShapeOperator_det_north hF hN hi hu ho x hn
  · have hs : x ∈ sphereSouthSource := by change (x : E3) 2 ≠ 1; linarith
    simpa only [sphereGaussianCurvature, hx, ↓reduceIte] using
      sphereShapeOperator_det_south hF hN hi hu ho x hs

theorem contMDiff_sphereGaussianCurvature {F N : SpherePoint → E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hu : ∀ x, ‖N x‖ = 1)
    (ho : ∀ x v, inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (sphereGaussianCurvature F N) := by
  have he : (fun x => LinearMap.det (sphereShapeOperator F N x).toLinearMap) =
      sphereGaussianCurvature F N :=
    funext (sphereShapeOperator_det_eq_gaussian hF hN hi hu ho)
  rw [← he]
  exact sphereShapeOperator_det_contMDiff hF hN hi hu ho

end ContinuousFlexibility

