import ContinuousFlexibility.Geometry.RadialMetricRigidity
import ContinuousFlexibility.Contracts.GraphFamilyImage

/-!
# The actual graph-disk orbit is nonconstant

The temporary constant-image hypothesis produces the genuine global map
`P⁻¹ ∘ Rₜ ∘ P`. Actual graph height uniqueness, differentiation, and ambient
Euclidean inner-product preservation prove that it is an intrinsic isometry.
Radial rigidity then contradicts the retained nonradial Core witness.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def IsometricGraphDevelopment.intrinsicRotationLift {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (t : ℝ) : PolarPoint ≃ₜ PolarPoint where
  toFun := fun x => D.planar.symm (planarRotation t (D.planar x))
  invFun := fun x => D.planar.symm (planarRotation (-t) (D.planar x))
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  continuous_toFun := D.planar.symm.continuous.comp
    ((planarRotation t).continuous.comp D.planar.continuous)
  continuous_invFun := D.planar.symm.continuous.comp
    ((planarRotation (-t)).continuous.comp D.planar.continuous)

@[simp] theorem IsometricGraphDevelopment.intrinsicRotationLift_apply
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    D.intrinsicRotationLift t x = D.planar.symm (planarRotation t (D.planar x)) := rfl

@[simp] theorem IsometricGraphDevelopment.intrinsicRotationLift_planar
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    D.planar (D.intrinsicRotationLift t x) = planarRotation t (D.planar x) := by
  simp

theorem IsometricGraphDevelopment.intrinsicRotationLift_smooth
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) :
    ContDiff ℝ ∞ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) :=
  D.smooth_inverse.comp ((planarRotation t).contDiff.comp D.smooth_planar)

theorem IsometricGraphDevelopment.intrinsicRotationLift_inverse_smooth
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) :
    ContDiff ℝ ∞ ((D.intrinsicRotationLift t).symm : PolarPoint → PolarPoint) :=
  D.smooth_inverse.comp ((planarRotation (-t)).contDiff.comp D.smooth_planar)

theorem IsometricGraphDevelopment.intrinsicRotationLift_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) : D.intrinsicRotationLift t x = planarRotation t x := by
  have hrot : D.planar (planarRotation t x) = planarRotation t x :=
    D.normalized_outside _ (by simpa using hx)
  change D.planar.symm (planarRotation t (D.planar x)) = planarRotation t x
  rw [D.normalized_outside x hx]
  simpa using (congrArg D.planar.symm hrot).symm

theorem IsometricGraphDevelopment.intrinsicRotationLift_image_disk
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {R : ℝ} (hR : A.b ≤ R) :
    D.intrinsicRotationLift t '' {x : PolarPoint | cartesianRadius x ≤ R} =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
  let S : Set PolarPoint := {x | cartesianRadius x ≤ R}
  have hP : D.planar '' S = S :=
    image_larger_disk_of_normalized_homeomorph D.planar hR D.normalized_outside
  calc
    D.intrinsicRotationLift t '' S =
        D.planar.symm '' (planarRotation t '' (D.planar '' S)) := by
      rw [image_image, image_image]
      rfl
    _ = D.planar.symm '' S := by rw [hP, planarRotation_image_closedCartesianDisk]
    _ = D.planar.symm '' (D.planar '' S) := by rw [hP]
    _ = S := by simp only [image_image, Homeomorph.symm_apply_apply, image_id']

/-- Actual graph image invariance gives an actual graph conjugacy on the full plane;
outside the physical disk this follows from the proved horizontal exterior. -/
theorem IsometricGraphDevelopment.map_intrinsicRotationLift_of_disk_invariant
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b ≤ R)
    (t : ℝ)
    (hinv : axialRotation t '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) =
      D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) (x : PolarPoint) :
    D.map (D.intrinsicRotationLift t x) = axialRotation t (D.map x) := by
  by_cases hx : cartesianRadius x ≤ R
  · have hm : axialRotation t (D.map x) ∈ D.map '' {x : PolarPoint | cartesianRadius x ≤ R} := by
      rw [← hinv]
      exact ⟨D.map x, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨y, _, hy⟩ := hm
    have hb : D.planar y = planarRotation t (D.planar x) := by
      simpa only [IsometricGraphDevelopment.map, graphBaseProjection_graphMap,
        axialRotation_apply, axialRotationMap_base] using congrArg graphBaseProjection hy
    have heq : y = D.intrinsicRotationLift t x := by
      apply D.planar.injective
      rw [D.intrinsicRotationLift_planar]
      exact hb
    rw [← heq]
    exact hy
  · have hb : A.b < cartesianRadius x := hR.trans_lt (lt_of_not_ge hx)
    apply e3_eq_of_base_height
    · simpa only [IsometricGraphDevelopment.map, graphBaseProjection_graphMap,
        axialRotation_apply, axialRotationMap_base] using D.intrinsicRotationLift_planar t x
    · simp only [IsometricGraphDevelopment.map, graphMap_two, axialRotation_apply,
        axialRotationMap_height]
      rw [D.intrinsicRotationLift_outside t hb,
        A.cartesianHeight_right (by simpa using hb.le), A.cartesianHeight_right hb.le]

theorem IsometricGraphDevelopment.height_intrinsicRotationLift_of_disk_invariant
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b ≤ R)
    (t : ℝ)
    (hinv : axialRotation t '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) =
      D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) (x : PolarPoint) :
    A.cartesianHeight (D.intrinsicRotationLift t x) = A.cartesianHeight x := by
  simpa only [IsometricGraphDevelopment.map, graphMap_two, axialRotation_apply,
    axialRotationMap_height] using congrArg (fun v : E3 => v 2)
      (D.map_intrinsicRotationLift_of_disk_invariant hR t hinv x)

/-- The intrinsic metric identity is derived from the real graph conjugacy and the
actual ambient Euclidean rotation, not assumed for the lifted map. -/
theorem IsometricGraphDevelopment.metric_intrinsicRotationLift_of_disk_invariant
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b ≤ R)
    (t : ℝ)
    (hinv : axialRotation t '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) =
      D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) (x u v : PolarPoint) :
    cartesianMetric A.w (D.intrinsicRotationLift t x)
      (fderiv ℝ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) x u)
      (fderiv ℝ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) x v) =
      cartesianMetric A.w x u v := by
  have hD : ContDiff ℝ ∞ D.map := D.smooth_graph
  have hH := D.intrinsicRotationLift_smooth t
  have hfun : D.map ∘ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) =
      (axialRotation t : E3 → E3) ∘ D.map := by
    funext y
    exact D.map_intrinsicRotationLift_of_disk_invariant hR t hinv y
  have hleft := (hD.differentiable (by simp) (D.intrinsicRotationLift t x)).hasFDerivAt.comp x
    (hH.differentiable (by simp) x).hasFDerivAt
  let T : E3 →L[ℝ] E3 := (axialRotation t).toLinearIsometry.toContinuousLinearMap
  have hT : (T : E3 → E3) = (axialRotation t : E3 → E3) := rfl
  have hright := T.hasFDerivAt.comp x
    (hD.differentiable (by simp) x).hasFDerivAt
  rw [hT] at hright
  have hd := congrArg (fun f : PolarPoint → E3 => fderiv ℝ f x) hfun
  rw [hleft.fderiv, hright.fderiv] at hd
  have hu : fderiv ℝ D.map (D.intrinsicRotationLift t x)
      (fderiv ℝ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) x u) =
        axialRotation t (fderiv ℝ D.map x u) := by
    simpa only [ContinuousLinearMap.comp_apply, hT] using
      congrArg (fun L : PolarPoint →L[ℝ] E3 => L u) hd
  have hv : fderiv ℝ D.map (D.intrinsicRotationLift t x)
      (fderiv ℝ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) x v) =
        axialRotation t (fderiv ℝ D.map x v) := by
    simpa only [ContinuousLinearMap.comp_apply, hT] using
      congrArg (fun L : PolarPoint →L[ℝ] E3 => L v) hd
  calc
    _ = inner ℝ
        (fderiv ℝ D.map (D.intrinsicRotationLift t x)
          (fderiv ℝ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) x u))
        (fderiv ℝ D.map (D.intrinsicRotationLift t x)
          (fderiv ℝ (D.intrinsicRotationLift t : PolarPoint → PolarPoint) x v)) :=
      (D.graph_metric _ _ _).symm
    _ = inner ℝ (axialRotation t (fderiv ℝ D.map x u))
        (axialRotation t (fderiv ℝ D.map x v)) := by rw [hu, hv]
    _ = inner ℝ (fderiv ℝ D.map x u) (fderiv ℝ D.map x v) := by
      simpa only [axialRotation_apply] using axialRotationMap_inner t
        (fderiv ℝ D.map x u) (fderiv ℝ D.map x v)
    _ = cartesianMetric A.w x u v := D.graph_metric x u v

theorem IsometricGraphDevelopment.intrinsicRotationLift_eq_rotation_of_disk_invariant
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R)
    (t : ℝ)
    (hinv : axialRotation t '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) =
      D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) :
    ∀ x : PolarPoint, D.intrinsicRotationLift t x = planarRotation t x := by
  have hclosed := A.metric_isometry_eq_rotation_on_closed_disk (D.intrinsicRotationLift_smooth t) hR
    (fun x _ u v => D.metric_intrinsicRotationLift_of_disk_invariant hR.le t hinv x u v) t
    (fun x hx _ => D.intrinsicRotationLift_outside t hx)
  intro x
  by_cases hx : cartesianRadius x ≤ R
  · exact hclosed x hx
  · exact D.intrinsicRotationLift_outside t (hR.trans (lt_of_not_ge hx))

theorem planarRotation_polarPosition (t r θ : ℝ) :
    planarRotation t (polarPosition r θ) = polarPosition r (θ + 2 * Real.pi * t) := by
  simp only [planarRotation, planeRotationLinearMap_apply, polarPosition, Real.cos_add, Real.sin_add]
  apply Prod.ext <;> dsimp only <;> ring

/-- The same constructed nonradial graph disk has at least one different phase image. -/
theorem IsometricGraphDevelopment.exists_rotationFamily_image_ne
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ t : ℝ,
      D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R} ≠
        D.map '' {x : PolarPoint | cartesianRadius x ≤ R} := by
  classical
  by_contra hnone
  have hall : ∀ t : ℝ,
      D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R} =
        D.map '' {x : PolarPoint | cartesianRadius x ≤ R} := by
    intro t
    by_contra hne
    exact hnone ⟨t, hne⟩
  have hinv : ∀ t : ℝ,
      axialRotation t '' (D.map '' {x : PolarPoint | cartesianRadius x ≤ R}) =
        D.map '' {x : PolarPoint | cartesianRadius x ≤ R} := by
    intro t
    simpa only [neg_neg] using (D.rotationFamily_image_closedDisk (-t) R).symm.trans (hall (-t))
  have hheight : ∀ t : ℝ, ∀ x : PolarPoint,
      A.cartesianHeight (planarRotation t x) = A.cartesianHeight x := by
    intro t x
    have h := D.height_intrinsicRotationLift_of_disk_invariant hR.le t (hinv t) x
    rwa [D.intrinsicRotationLift_eq_rotation_of_disk_invariant hR t (hinv t) x] at h
  obtain ⟨r, hr, θ, φ, hne⟩ := A.nonradial
  have hr0 : 0 < r := A.a_pos.trans hr.1
  let t := (φ - θ) / (2 * Real.pi)
  have ht : θ + 2 * Real.pi * t = φ := by
    dsimp [t]
    field_simp [Real.pi_ne_zero]
    ring
  have hz := hheight t (polarPosition r θ)
  rw [planarRotation_polarPosition, ht] at hz
  have hzeq : A.z (r, φ) = A.z (r, θ) := by
    simpa only [A.cartesianHeight_polarPosition hr0] using hz
  exact hne hzeq.symm

theorem IsometricGraphDevelopment.exists_distinct_rotationFamily_images
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) {R : ℝ} (hR : A.b < R) :
    ∃ s t : ℝ,
      D.rotationFamily s '' {x : PolarPoint | cartesianRadius x ≤ R} ≠
        D.rotationFamily t '' {x : PolarPoint | cartesianRadius x ≤ R} := by
  obtain ⟨t, ht⟩ := D.exists_rotationFamily_image_ne hR
  refine ⟨t, 0, ?_⟩
  have hzero : D.rotationFamily 0 = D.map := funext D.rotationFamily_zero
  rwa [hzero]

end ContinuousFlexibility
