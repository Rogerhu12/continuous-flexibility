import ContinuousFlexibility.Geometry.CoframeCurvature
import ContinuousFlexibility.Geometry.FlatDevelopment
import ContinuousFlexibility.Scalar.FormPullback

/-!
# Actual coordinate derivatives for planar Euclidean rigidity

The relative SO(2) coefficients are actual partial derivatives. Their
Cauchy--Riemann relations follow from the actual derivative metric and its
orientation, and the second-derivative argument uses genuine mixed partials.
-/

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def planeRotationLinearMap (c s : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  (c • ContinuousLinearMap.fst ℝ ℝ ℝ - s • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (s • ContinuousLinearMap.fst ℝ ℝ ℝ + c • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem planeRotationLinearMap_apply (c s : ℝ) (v : PolarPoint) :
    planeRotationLinearMap c s v = (c * v.1 - s * v.2, s * v.1 + c * v.2) := by
  simp [planeRotationLinearMap, smul_eq_mul]

theorem planeRotationLinearMap_metric {c s : ℝ} (hu : c ^ 2 + s ^ 2 = 1)
    (u v : PolarPoint) :
    coordinateEuclideanPair (planeRotationLinearMap c s u) (planeRotationLinearMap c s v) =
      coordinateEuclideanPair u v := by
  rw [planeRotationLinearMap_apply, planeRotationLinearMap_apply]
  unfold coordinateEuclideanPair
  dsimp only
  linear_combination (u.1 * v.1 + u.2 * v.2) * hu

theorem planeRotationLinearMap_bijective {c s : ℝ} (hu : c ^ 2 + s ^ 2 = 1) :
    Function.Bijective (planeRotationLinearMap c s) := by
  let η₁ : PlaneOneForm := ⟨fun _ => c, fun _ => -s⟩
  let η₂ : PlaneOneForm := ⟨fun _ => s, fun _ => c⟩
  have heq : planeRotationLinearMap c s = coframeLinearMap η₁ η₂ 0 := by
    apply ContinuousLinearMap.ext
    intro v
    simp [planeRotationLinearMap_apply, coframeLinearMap, η₁, η₂,
      PlaneOneForm.toCLM, smul_eq_mul]
    ring
  rw [heq]
  apply coframeLinearMap_bijective
  have hw : wedgeCoefficient η₁ η₂ 0 = 1 := by
    change c * c - -s * s = 1
    nlinarith
  rw [hw]
  exact one_ne_zero

def derivativeRotationCos (P : PolarPoint → PolarPoint) : PolarPoint → ℝ :=
  radialPartial (fun x => (P x).1)

def derivativeRotationSin (P : PolarPoint → PolarPoint) : PolarPoint → ℝ :=
  radialPartial (fun x => (P x).2)

theorem fderiv_plane_coordinates {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hP : DifferentiableAt ℝ P x) (v : PolarPoint) :
    fderiv ℝ P x v =
      (v.1 * radialPartial (fun y => (P y).1) x + v.2 * angularPartial (fun y => (P y).1) x,
       v.1 * radialPartial (fun y => (P y).2) x + v.2 * angularPartial (fun y => (P y).2) x) := by
  apply Prod.ext
  · have h := polarCLM_apply_decompose (fderiv ℝ (fun y => (P y).1) x) v
    simpa only [radialPartial, angularPartial, hP.hasFDerivAt.fst.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] using h
  · have h := polarCLM_apply_decompose (fderiv ℝ (fun y => (P y).2) x) v
    simpa only [radialPartial, angularPartial, hP.hasFDerivAt.snd.fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] using h

theorem derivative_rotation_of_metric {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hP : DifferentiableAt ℝ P x)
    (hm : ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    (hJ : 0 < planeJacobian P x) :
    derivativeRotationCos P x ^ 2 + derivativeRotationSin P x ^ 2 = 1 ∧
      angularPartial (fun y => (P y).1) x = -derivativeRotationSin P x ∧
      angularPartial (fun y => (P y).2) x = derivativeRotationCos P x := by
  have h1 := hm (1, 0) (1, 0)
  have h2 := hm (0, 1) (0, 1)
  have h3 := hm (1, 0) (0, 1)
  simp only [coordinateEuclideanPair] at h1 h2 h3
  have hr := oriented_coframe_rotation_algebra (a := 1) (b := 0) (c := 0) (d := 1)
    (u := (fderiv ℝ P x (1, 0)).1) (v := (fderiv ℝ P x (0, 1)).1)
    (s := (fderiv ℝ P x (1, 0)).2) (t := (fderiv ℝ P x (0, 1)).2)
    (by nlinarith [h1]) (by nlinarith [h2]) (by nlinarith [h3])
    (by simpa only [planeJacobian, one_mul, mul_one, zero_mul, mul_zero, sub_zero,
      mul_comm] using hJ)
  simp only [mul_one, mul_zero, sub_zero, zero_sub, div_one,
    zero_add, add_zero] at hr
  simp only [derivativeRotationCos, derivativeRotationSin, radialPartial, angularPartial,
    hP.hasFDerivAt.fst.fderiv, hP.hasFDerivAt.snd.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  exact ⟨by nlinarith [hr.1, hr.2.2.2.1], by linarith [hr.2.2.2.1], hr.2.2.2.2⟩

theorem fderiv_eq_planeRotation_of_metric {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hP : DifferentiableAt ℝ P x)
    (hm : ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    (hJ : 0 < planeJacobian P x) :
    fderiv ℝ P x = planeRotationLinearMap (derivativeRotationCos P x) (derivativeRotationSin P x) := by
  obtain ⟨_, h1, h2⟩ := derivative_rotation_of_metric hP hm hJ
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_plane_coordinates hP, planeRotationLinearMap_apply, h1, h2]
  change (v.1 * derivativeRotationCos P x + v.2 * -derivativeRotationSin P x,
    v.1 * derivativeRotationSin P x + v.2 * derivativeRotationCos P x) = _
  apply Prod.ext <;> dsimp only <;> ring

/-- The SO(2) coefficients of a genuine orientation-preserving Euclidean derivative
have zero actual derivative. The proof differentiates their true first partials. -/
theorem derivative_rotation_fderiv_zero
    {P : PolarPoint → PolarPoint} {U : Set PolarPoint} (hU : IsOpen U)
    (hP : ∀ x ∈ U, ContDiffAt ℝ ∞ P x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    (hJ : ∀ x ∈ U, 0 < planeJacobian P x) {x : PolarPoint} (hx : x ∈ U) :
    fderiv ℝ (derivativeRotationCos P) x = 0 ∧ fderiv ℝ (derivativeRotationSin P) x = 0 := by
  let C := derivativeRotationCos P
  let S := derivativeRotationSin P
  have hCx : ContDiffAt ℝ ∞ C x := contDiffAt_radialPartial (hP x hx).fst (by simp)
  have hSx : ContDiffAt ℝ ∞ S x := contDiffAt_radialPartial (hP x hx).snd (by simp)
  have hunit : (fun y => C y ^ 2 + S y ^ 2) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (derivative_rotation_of_metric ((hP y hy).differentiableAt (by simp))
      (hm y hy) (hJ y hy)).1
  obtain ⟨hu, hr, hθ⟩ := so2_unit_tangent
    (hCx.differentiableAt (by simp)) (hSx.differentiableAt (by simp)) hunit
  have hCR₁ : angularPartial (fun y => (P y).1) =ᶠ[𝓝 x] fun y => -S y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (derivative_rotation_of_metric ((hP y hy).differentiableAt (by simp))
      (hm y hy) (hJ y hy)).2.1
  have hCR₂ : angularPartial (fun y => (P y).2) =ᶠ[𝓝 x] C := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (derivative_rotation_of_metric ((hP y hy).differentiableAt (by simp))
      (hm y hy) (hJ y hy)).2.2
  have hCθ : angularPartial C x = -radialPartial S x := by
    change angularPartial (radialPartial (fun y => (P y).1)) x = _
    rw [← radial_angular_commute ((hP x hx).fst.of_le (by simp))]
    unfold radialPartial
    rw [hCR₁.fderiv_eq, fderiv_fun_neg]
    simp
  have hSθ : angularPartial S x = radialPartial C x := by
    change angularPartial (radialPartial (fun y => (P y).2)) x = _
    rw [← radial_angular_commute ((hP x hx).snd.of_le (by simp))]
    unfold radialPartial
    rw [hCR₂.fderiv_eq]
  rw [hCθ, hSθ] at hθ
  have hCr : radialPartial C x = 0 := by
    linear_combination C x * hr + S x * hθ - radialPartial C x * hu
  have hSr : radialPartial S x = 0 := by
    linear_combination S x * hr - C x * hθ - radialPartial S x * hu
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    rw [polarCLM_apply_decompose]
    change v.1 * radialPartial C x + v.2 * angularPartial C x = 0
    rw [hCr, hCθ, hSr]
    ring
  · apply ContinuousLinearMap.ext
    intro v
    rw [polarCLM_apply_decompose]
    change v.1 * radialPartial S x + v.2 * angularPartial S x = 0
    rw [hSr, hSθ, hCr]
    ring

end ContinuousFlexibility
