import ContinuousFlexibility.Contracts.DevelopmentSymmetry
import ContinuousFlexibility.Geometry.EuclideanRigidity
import ContinuousFlexibility.Geometry.PlanarOrientation
import Mathlib.Analysis.Convex.PathConnected

/-!
# Uniqueness, oddness and the centered inner disk

These are consequences of the constructed development, rather than extra
fields imposed on the annular core. Euclidean rigidity uses the actual
coordinate pairing, since the coordinate product has the max norm.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem IsometricGraphDevelopment.planar_unique
    {A : FlatAnnularCore} (D E : IsometricGraphDevelopment A) :
    (D.planar : PolarPoint → PolarPoint) = (E.planar : PolarPoint → PolarPoint) := by
  apply normalized_developments_unique D.planar E.planar D.smooth_planar
    D.smooth_inverse E.smooth_planar
    (fun x u v => (D.remainder_metric x u v).trans (E.remainder_metric x u v).symm)
    (isOpen_lt continuous_const continuous_cartesianRadius)
  · refine ⟨polarPosition (A.b + 1) 0, ?_⟩
    change A.b < cartesianRadius (polarPosition (A.b + 1) 0)
    rw [cartesianRadius_polarPosition (by linarith [A.b_pos])]
    linarith
  · intro x hx
    exact D.normalized_outside x hx
  · intro x hx
    exact E.normalized_outside x hx

theorem IsometricGraphDevelopment.planar_odd
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) (x : PolarPoint) :
    D.planar (-x) = -D.planar x := by
  have h := congrFun (D.planar_unique D.reflected) x
  change D.planar x = -D.planar (-x) at h
  simpa using congrArg Neg.neg h.symm

@[simp] theorem IsometricGraphDevelopment.planar_zero
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) : D.planar 0 = 0 := by
  have h := D.planar_odd 0
  simp only [neg_zero] at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext <;> dsimp at * <;> linarith

theorem convex_cartesianDisk (R : ℝ) : Convex ℝ {x : PolarPoint | cartesianRadius x < R} := by
  have h := (convex_ball (0 : ℂ) R).linear_preimage
    Complex.equivRealProdCLM.symm.toLinearMap
  have heq : Complex.equivRealProdCLM.symm.toLinearMap ⁻¹' Metric.ball (0 : ℂ) R =
      {x : PolarPoint | cartesianRadius x < R} := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
    rfl
  rwa [heq] at h

theorem closure_cartesianDisk {R : ℝ} (hR : 0 < R) :
    closure {x : PolarPoint | cartesianRadius x < R} =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
  have h := Complex.equivRealProdCLM.symm.toHomeomorph.preimage_closure
    (Metric.ball (0 : ℂ) R)
  rw [closure_ball (0 : ℂ) hR.ne'] at h
  have ho : Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' Metric.ball (0 : ℂ) R =
      {x : PolarPoint | cartesianRadius x < R} := by
    ext x
    simp [cartesianRadius]
  have hc : Complex.equivRealProdCLM.symm.toHomeomorph ⁻¹' Metric.closedBall (0 : ℂ) R =
      {x : PolarPoint | cartesianRadius x ≤ R} := by
    ext x
    simp [cartesianRadius]
  simpa only [ho, hc] using h.symm

/-- Exterior normalization and half-turn symmetry remove the translation
in the inner Euclidean rigidity theorem. The conclusion includes its boundary. -/
theorem IsometricGraphDevelopment.exists_centered_inner_rotation
    {A : FlatAnnularCore} (D : IsometricGraphDevelopment A) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      (∀ x : PolarPoint, cartesianRadius x ≤ A.a →
        D.planar x = planeRotationLinearMap c s x) ∧
      ∀ x : PolarPoint, cartesianRadius x < A.a →
        fderiv ℝ (D.planar : PolarPoint → PolarPoint) x = planeRotationLinearMap c s := by
  have hzero : cartesianRadius (0 : PolarPoint) < A.a := by
    simpa [cartesianRadius] using A.a_pos
  obtain ⟨c, s, b, hu, hmap, hder⟩ := exists_rotation_affine_of_euclidean_derivative
    (isOpen_lt continuous_cartesianRadius continuous_const)
    (convex_cartesianDisk A.a).isPreconnected ⟨0, hzero⟩
    (fun _ _ => D.smooth_planar.contDiffAt)
    (fun x hx u v => (D.remainder_metric x u v).trans (A.cartesianRemainder_left hx u v))
    (fun x _ => D.planar_orientation x)
  have hb : b = 0 := by
    have h := hmap 0 hzero
    simpa only [D.planar_zero, map_zero, zero_add] using h.symm
  have hopen : Set.EqOn (D.planar : PolarPoint → PolarPoint)
      (planeRotationLinearMap c s) {x : PolarPoint | cartesianRadius x < A.a} := by
    intro x hx
    simpa only [hb, add_zero] using hmap x hx
  have hclosed := hopen.closure D.smooth_planar.continuous
    (planeRotationLinearMap c s).continuous
  rw [closure_cartesianDisk A.a_pos] at hclosed
  exact ⟨c, s, hu, fun x hx => hclosed hx, fun x hx => hder x hx⟩

end ContinuousFlexibility
