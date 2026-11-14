module

public import ContinuousFlexibility.Geometry.PlanarRotations
public import ContinuousFlexibility.Contracts.CenteredDevelopment

/-!
# The actual rotation-conjugated Euclidean graph family

For the paper's phase convention, the planar map is `R₋ₜ ∘ P ∘ Rₜ`, and the
height is `Z ∘ Rₜ`. One fixed constructed development supplies every member.
Joint smoothness, the intrinsic metric, and the fixed collars are proved from
the actual formulas. This file makes no sphere-closure or noncongruence claim.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rotationConjugate (t : ℝ) (P : PolarPoint ≃ₜ PolarPoint) : PolarPoint ≃ₜ PolarPoint where
  toFun := fun x => planarRotation (-t) (P (planarRotation t x))
  invFun := fun x => planarRotation (-t) (P.symm (planarRotation t x))
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  continuous_toFun := (planarRotation (-t)).continuous.comp
    (P.continuous.comp (planarRotation t).continuous)
  continuous_invFun := (planarRotation (-t)).continuous.comp
    (P.symm.continuous.comp (planarRotation t).continuous)

@[simp] theorem rotationConjugate_apply (t : ℝ) (P : PolarPoint ≃ₜ PolarPoint)
    (x : PolarPoint) :
    rotationConjugate t P x = planarRotation (-t) (P (planarRotation t x)) := rfl

def rotatedHeight (t : ℝ) (Z : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun x => Z (planarRotation t x)

theorem contDiff_rotationConjugate (t : ℝ) (P : PolarPoint ≃ₜ PolarPoint)
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint)) :
    ContDiff ℝ ∞ (rotationConjugate t P : PolarPoint → PolarPoint) :=
  (planarRotation (-t)).contDiff.comp (hP.comp (planarRotation t).contDiff)

theorem contDiff_rotatedHeight (t : ℝ) {Z : PolarPoint → ℝ} (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (rotatedHeight t Z) := hZ.comp (planarRotation t).contDiff

theorem contDiff_rotationConjugate_joint (P : PolarPoint ≃ₜ PolarPoint)
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint)) :
    ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => rotationConjugate q.1 P q.2) := by
  have hinner : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => P (planarRotation q.1 q.2)) :=
    hP.comp contDiff_planarRotation_joint
  have ha : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => 2 * Real.pi * (-q.1)) :=
    contDiff_const.mul contDiff_fst.neg
  have h := ((ha.cos.mul hinner.fst).sub (ha.sin.mul hinner.snd)).prodMk
    ((ha.sin.mul hinner.fst).add (ha.cos.mul hinner.snd))
  simpa only [rotationConjugate_apply, planarRotation, planeRotationLinearMap_apply] using h

def IsometricGraphDevelopment.rotationFamily {A : FlatAnnularCore}
    (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) : E3 :=
  graphMap (rotationConjugate t D.planar) (rotatedHeight t A.cartesianHeight) x

theorem IsometricGraphDevelopment.rotationFamily_joint_smooth
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => D.rotationFamily q.1 q.2) := by
  have hp := contDiff_rotationConjugate_joint D.planar D.smooth_planar
  have hz : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => A.cartesianHeight (planarRotation q.1 q.2)) :=
    A.contDiff_cartesianHeight.comp contDiff_planarRotation_joint
  exact ((hp.fst.smul_const (e3Basis 0)).add (hp.snd.smul_const (e3Basis 1))).add
    (hz.smul_const (e3Basis 2))

theorem IsometricGraphDevelopment.rotationFamily_smooth
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) :
    ContDiff ℝ ∞ (D.rotationFamily t) :=
  contDiff_graphMap (contDiff_rotationConjugate t D.planar D.smooth_planar)
    (contDiff_rotatedHeight t A.contDiff_cartesianHeight)

theorem IsometricGraphDevelopment.rotationFamily_periodic
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    Function.Periodic D.rotationFamily 1 := by
  intro t
  funext x
  simp only [IsometricGraphDevelopment.rotationFamily, graphMap, rotationConjugate_apply,
    rotatedHeight, planarRotation_add_one, planarRotation_neg_add_one]

@[simp] theorem IsometricGraphDevelopment.rotationFamily_zero
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    D.rotationFamily 0 x = D.map x := by
  simp [IsometricGraphDevelopment.rotationFamily, IsometricGraphDevelopment.map,
    graphMap, rotationConjugate_apply, rotatedHeight]

theorem IsometricGraphDevelopment.rotationFamily_embedding
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) :
    Topology.IsEmbedding (D.rotationFamily t) :=
  isEmbedding_graphMap (rotationConjugate t D.planar)
    (contDiff_rotatedHeight t A.contDiff_cartesianHeight).continuous

theorem IsometricGraphDevelopment.rotationFamily_embedding_restrict
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (S : Set PolarPoint) :
    Topology.IsEmbedding (fun x : S => D.rotationFamily t x) :=
  isEmbedding_graphMap_restrict (rotationConjugate t D.planar)
    (contDiff_rotatedHeight t A.contDiff_cartesianHeight).continuous S

theorem fderiv_rotationConjugate (t : ℝ) (P : PolarPoint ≃ₜ PolarPoint)
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint)) (x : PolarPoint) :
    fderiv ℝ (rotationConjugate t P : PolarPoint → PolarPoint) x =
      (planarRotation (-t)).comp
        ((fderiv ℝ (P : PolarPoint → PolarPoint) (planarRotation t x)).comp (planarRotation t)) := by
  have h := (planarRotation (-t)).hasFDerivAt.comp x
    ((hP.differentiable (by simp) (planarRotation t x)).hasFDerivAt.comp x
      (planarRotation t).hasFDerivAt)
  exact h.fderiv

theorem fderiv_rotatedHeight (t : ℝ) {Z : PolarPoint → ℝ} (hZ : ContDiff ℝ ∞ Z)
    (x : PolarPoint) :
    fderiv ℝ (rotatedHeight t Z) x =
      (fderiv ℝ Z (planarRotation t x)).comp (planarRotation t) :=
  ((hZ.differentiable (by simp) (planarRotation t x)).hasFDerivAt.comp x
    (planarRotation t).hasFDerivAt).fderiv

theorem IsometricGraphDevelopment.rotationFamily_remainder_metric
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x u v : PolarPoint) :
    coordinateEuclideanPair
      (fderiv ℝ (rotationConjugate t D.planar : PolarPoint → PolarPoint) x u)
      (fderiv ℝ (rotationConjugate t D.planar : PolarPoint → PolarPoint) x v) =
        cartesianRemainder A.w (rotatedHeight t A.cartesianHeight) x u v := by
  rw [fderiv_rotationConjugate t D.planar D.smooth_planar]
  simp only [ContinuousLinearMap.comp_apply]
  rw [planarRotation_metric, D.remainder_metric]
  unfold cartesianRemainder
  rw [cartesianMetric_planarRotation, fderiv_rotatedHeight t A.contDiff_cartesianHeight]
  rfl

theorem IsometricGraphDevelopment.rotationFamily_metric
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x u v : PolarPoint) :
    inner ℝ (fderiv ℝ (D.rotationFamily t) x u) (fderiv ℝ (D.rotationFamily t) x v) =
      cartesianMetric A.w x u v :=
  graphMap_pullback_metric
    ((contDiff_rotationConjugate t D.planar D.smooth_planar).differentiable (by simp) x)
    ((contDiff_rotatedHeight t A.contDiff_cartesianHeight).differentiable (by simp) x)
    (D.rotationFamily_remainder_metric t x) u v

theorem IsometricGraphDevelopment.rotationFamily_immersion
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) (x : PolarPoint) :
    Function.Injective (fderiv ℝ (D.rotationFamily t) x) :=
  graphMap_fderiv_injective_of_metric
    ((contDiff_rotationConjugate t D.planar D.smooth_planar).differentiable (by simp) x)
    ((contDiff_rotatedHeight t A.contDiff_cartesianHeight).differentiable (by simp) x)
    (D.rotationFamily_remainder_metric t x)

theorem IsometricGraphDevelopment.rotationFamily_fixed_outside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {x : PolarPoint}
    (hx : A.b < cartesianRadius x) : D.rotationFamily t x = D.map x := by
  have hp : rotationConjugate t D.planar x = D.planar x := by
    rw [rotationConjugate_apply, D.normalized_outside _ (by simpa using hx),
      planarRotation_cancel_neg, D.normalized_outside _ hx]
  have hz : rotatedHeight t A.cartesianHeight x = A.cartesianHeight x := by
    change A.cartesianHeight (planarRotation t x) = A.cartesianHeight x
    rw [A.cartesianHeight_right (by simpa using hx.le), A.cartesianHeight_right hx.le]
  simp only [IsometricGraphDevelopment.rotationFamily, IsometricGraphDevelopment.map,
    graphMap, hp, hz]

theorem IsometricGraphDevelopment.rotationFamily_fixed_inside
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (t : ℝ) {x : PolarPoint}
    (hx : cartesianRadius x ≤ A.a) : D.rotationFamily t x = D.map x := by
  obtain ⟨c, s, _, hinner, _⟩ := D.exists_centered_inner_rotation
  have hp : rotationConjugate t D.planar x = D.planar x := by
    rw [rotationConjugate_apply, hinner _ (by simpa using hx), hinner x hx,
      planarRotation_commute, planarRotation_cancel_neg]
  have hz : rotatedHeight t A.cartesianHeight x = A.cartesianHeight x := by
    change A.cartesianHeight (planarRotation t x) = A.cartesianHeight x
    rw [A.cartesianHeight_left (by simpa using hx), A.cartesianHeight_left hx]
  simp only [IsometricGraphDevelopment.rotationFamily, IsometricGraphDevelopment.map,
    graphMap, hp, hz]

end ContinuousFlexibility
