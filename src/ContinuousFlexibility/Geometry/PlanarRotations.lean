module

public import ContinuousFlexibility.Geometry.EuclideanRigidityCoordinates
public import ContinuousFlexibility.Contracts.CartesianMetric

/-!
# Actual rotations of the Cartesian coordinate plane

The parameter is measured in turns. Metric and radius statements refer to the
coordinate Euclidean pairing and the genuine complex norm, never the product norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def planarRotation (t : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  planeRotationLinearMap (Real.cos (2 * Real.pi * t)) (Real.sin (2 * Real.pi * t))

theorem planeRotationLinearMap_commute (c s d e : ℝ) (x : PolarPoint) :
    planeRotationLinearMap c s (planeRotationLinearMap d e x) =
      planeRotationLinearMap d e (planeRotationLinearMap c s x) := by
  simp only [planeRotationLinearMap_apply]
  apply Prod.ext <;> dsimp only <;> ring

theorem planarRotation_metric (t : ℝ) (u v : PolarPoint) :
    coordinateEuclideanPair (planarRotation t u) (planarRotation t v) =
      coordinateEuclideanPair u v :=
  planeRotationLinearMap_metric (Real.cos_sq_add_sin_sq _) u v

@[simp] theorem planarRotation_zero (x : PolarPoint) : planarRotation 0 x = x := by
  simp [planarRotation, planeRotationLinearMap_apply]

theorem planarRotation_add (t s : ℝ) (x : PolarPoint) :
    planarRotation (t + s) x = planarRotation t (planarRotation s x) := by
  have ha : 2 * Real.pi * (t + s) = 2 * Real.pi * t + 2 * Real.pi * s := by ring
  simp only [planarRotation, planeRotationLinearMap_apply, ha, Real.cos_add, Real.sin_add]
  apply Prod.ext <;> dsimp only <;> ring

@[simp] theorem planarRotation_neg_cancel (t : ℝ) (x : PolarPoint) :
    planarRotation t (planarRotation (-t) x) = x := by
  rw [← planarRotation_add, add_neg_cancel, planarRotation_zero]

@[simp] theorem planarRotation_cancel_neg (t : ℝ) (x : PolarPoint) :
    planarRotation (-t) (planarRotation t x) = x := by
  rw [← planarRotation_add, neg_add_cancel, planarRotation_zero]

theorem planarRotation_commute (t c s : ℝ) (x : PolarPoint) :
    planarRotation t (planeRotationLinearMap c s x) =
      planeRotationLinearMap c s (planarRotation t x) :=
  planeRotationLinearMap_commute _ _ _ _ x

theorem planarRotation_add_one (t : ℝ) : planarRotation (t + 1) = planarRotation t := by
  have ha : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
  simp [planarRotation, ha, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem planarRotation_neg_add_one (t : ℝ) :
    planarRotation (-(t + 1)) = planarRotation (-t) := by
  have h := planarRotation_add_one (-(t + 1))
  have ha : -(t + 1) + 1 = -t := by ring
  rw [ha] at h
  exact h.symm

def planarRotationHomeomorph (t : ℝ) : PolarPoint ≃ₜ PolarPoint where
  toFun := planarRotation t
  invFun := planarRotation (-t)
  left_inv := planarRotation_cancel_neg t
  right_inv := planarRotation_neg_cancel t
  continuous_toFun := (planarRotation t).continuous
  continuous_invFun := (planarRotation (-t)).continuous

@[simp] theorem planarRotationHomeomorph_apply (t : ℝ) (x : PolarPoint) :
    planarRotationHomeomorph t x = planarRotation t x := rfl

@[simp] theorem planarRotationHomeomorph_symm_apply (t : ℝ) (x : PolarPoint) :
    (planarRotationHomeomorph t).symm x = planarRotation (-t) x := rfl

theorem contDiff_planarRotation_joint :
    ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => planarRotation q.1 q.2) := by
  have ha : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => 2 * Real.pi * q.1) :=
    contDiff_const.mul contDiff_fst
  have hx : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => q.2.1) := contDiff_snd.fst
  have hy : ContDiff ℝ ∞ (fun q : ℝ × PolarPoint => q.2.2) := contDiff_snd.snd
  exact ((ha.cos.mul hx).sub (ha.sin.mul hy)).prodMk
    ((ha.sin.mul hx).add (ha.cos.mul hy))

theorem cartesianRadius_sq_coordinates (x : PolarPoint) :
    cartesianRadius x ^ 2 = coordinateEuclideanPair x x := by
  simp [cartesianRadius, Complex.sq_norm, Complex.normSq_apply,
    Complex.equivRealProdCLM_symm_apply, coordinateEuclideanPair]

@[simp] theorem cartesianRadius_planarRotation (t : ℝ) (x : PolarPoint) :
    cartesianRadius (planarRotation t x) = cartesianRadius x := by
  have hsq : cartesianRadius (planarRotation t x) ^ 2 = cartesianRadius x ^ 2 := by
    rw [cartesianRadius_sq_coordinates, planarRotation_metric, cartesianRadius_sq_coordinates]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem cartesianMetric_planarRotation (w : ℝ → ℝ) (t : ℝ) (x u v : PolarPoint) :
    cartesianMetric w (planarRotation t x) (planarRotation t u) (planarRotation t v) =
      cartesianMetric w x u v := by
  simp only [cartesianMetric, cartesianProfileFactor, cartesianRadius_planarRotation,
    planarRotation_metric]

end ContinuousFlexibility
