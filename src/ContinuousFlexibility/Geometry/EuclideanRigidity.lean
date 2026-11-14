module

public import ContinuousFlexibility.Geometry.EuclideanRigidityCoordinates
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Actual planar Euclidean rigidity and normalized uniqueness

The product coordinate norm is not used as the Euclidean metric. A map whose
actual derivative preserves the coordinate Euclidean pairing is proved affine
on a connected open set. The proof does not assume a rigidity conclusion or
choose a global angle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Filter Set
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem exists_rotation_affine_of_euclidean_derivative
    {P : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    (hP : ∀ x ∈ U, ContDiffAt ℝ ∞ P x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    (hJ : ∀ x ∈ U, 0 < planeJacobian P x) :
    ∃ c s : ℝ, ∃ b : PolarPoint, c ^ 2 + s ^ 2 = 1 ∧
      (∀ x ∈ U, P x = planeRotationLinearMap c s x + b) ∧
      ∀ x ∈ U, fderiv ℝ P x = planeRotationLinearMap c s := by
  have hCs : ∀ x ∈ U, ContDiffAt ℝ ∞ (derivativeRotationCos P) x :=
    fun x hx => contDiffAt_radialPartial (hP x hx).fst (by simp)
  have hSs : ∀ x ∈ U, ContDiffAt ℝ ∞ (derivativeRotationSin P) x :=
    fun x hx => contDiffAt_radialPartial (hP x hx).snd (by simp)
  obtain ⟨c, hC⟩ := hU.exists_is_const_of_fderiv_eq_zero hc
    (fun x hx => ((hCs x hx).differentiableAt (by simp)).differentiableWithinAt)
    (fun x hx => (derivative_rotation_fderiv_zero hU hP hm hJ hx).1)
  obtain ⟨s, hS⟩ := hU.exists_is_const_of_fderiv_eq_zero hc
    (fun x hx => ((hSs x hx).differentiableAt (by simp)).differentiableWithinAt)
    (fun x hx => (derivative_rotation_fderiv_zero hU hP hm hJ hx).2)
  obtain ⟨x₀, hx₀⟩ := hne
  have hunit : c ^ 2 + s ^ 2 = 1 := by
    have hu := (derivative_rotation_of_metric ((hP x₀ hx₀).differentiableAt (by simp))
      (hm x₀ hx₀) (hJ x₀ hx₀)).1
    rwa [hC x₀ hx₀, hS x₀ hx₀] at hu
  have hder : ∀ x ∈ U, fderiv ℝ P x = planeRotationLinearMap c s := by
    intro x hx
    rw [fderiv_eq_planeRotation_of_metric ((hP x hx).differentiableAt (by simp))
      (hm x hx) (hJ x hx), hC x hx, hS x hx]
  obtain ⟨b, hb⟩ := hU.exists_eq_add_of_fderiv_eq hc
    (fun x hx => ((hP x hx).differentiableAt (by simp)).differentiableWithinAt)
    (planeRotationLinearMap c s).differentiable.differentiableOn
    (fun x hx => (hder x hx).trans (planeRotationLinearMap c s).hasFDerivAt.fderiv.symm)
  exact ⟨c, s, b, hunit, fun x hx => hb hx, hder⟩

/-- The linear part is a continuous linear equivalence which preserves the actual
coordinate Euclidean pairing. No max-norm `LinearIsometry` is asserted. -/
theorem exists_affine_of_euclidean_derivative
    {P : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    (hP : ∀ x ∈ U, ContDiffAt ℝ ∞ P x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    (hJ : ∀ x ∈ U, 0 < planeJacobian P x) :
    ∃ (L : PolarPoint ≃L[ℝ] PolarPoint) (b : PolarPoint),
      (∀ u v, coordinateEuclideanPair (L u) (L v) = coordinateEuclideanPair u v) ∧
      (∀ x ∈ U, P x = L x + b) ∧
      ∀ x ∈ U, fderiv ℝ P x = (L : PolarPoint →L[ℝ] PolarPoint) := by
  obtain ⟨c, s, b, hu, hmap, hder⟩ :=
    exists_rotation_affine_of_euclidean_derivative hU hc hne hP hm hJ
  let L := planeLinearEquivOfBijective (planeRotationLinearMap c s) (planeRotationLinearMap_bijective hu)
  have heq : (L : PolarPoint →L[ℝ] PolarPoint) = planeRotationLinearMap c s :=
    planeLinearEquivOfBijective_coe _ _
  have happly : ∀ v, L v = planeRotationLinearMap c s v := fun _ => rfl
  refine ⟨L, b, ?_, ?_, ?_⟩
  · intro u v
    simpa only [happly] using planeRotationLinearMap_metric hu u v
  · intro x hx
    simpa only [happly] using hmap x hx
  · intro x hx
    simpa only [heq] using hder x hx

theorem contDiffAt_planeJacobian {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hP : ContDiffAt ℝ ∞ P x) : ContDiffAt ℝ ∞ (planeJacobian P) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ P) x := hP.fderiv_right (by simp)
  have hr := hd.clm_apply (contDiffAt_const (c := ((1, 0) : PolarPoint)))
  have hθ := hd.clm_apply (contDiffAt_const (c := ((0, 1) : PolarPoint)))
  exact (hr.fst.mul hθ.snd).sub (hr.snd.mul hθ.fst)

theorem planeJacobian_sq_of_euclidean_derivative {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hm : ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v) :
    planeJacobian P x ^ 2 = 1 := by
  have h1 : (fderiv ℝ P x (1, 0)).1 ^ 2 + (fderiv ℝ P x (1, 0)).2 ^ 2 = 1 := by
    simpa [coordinateEuclideanPair, pow_two] using hm (1, 0) (1, 0)
  have h2 : (fderiv ℝ P x (0, 1)).1 ^ 2 + (fderiv ℝ P x (0, 1)).2 ^ 2 = 1 := by
    simpa [coordinateEuclideanPair, pow_two] using hm (0, 1) (0, 1)
  have h3 : (fderiv ℝ P x (1, 0)).1 * (fderiv ℝ P x (0, 1)).1 +
      (fderiv ℝ P x (1, 0)).2 * (fderiv ℝ P x (0, 1)).2 = 0 := by
    simpa [coordinateEuclideanPair] using hm (1, 0) (0, 1)
  unfold planeJacobian
  calc
    _ = ((fderiv ℝ P x (1, 0)).1 ^ 2 + (fderiv ℝ P x (1, 0)).2 ^ 2) *
        ((fderiv ℝ P x (0, 1)).1 ^ 2 + (fderiv ℝ P x (0, 1)).2 ^ 2) -
        ((fderiv ℝ P x (1, 0)).1 * (fderiv ℝ P x (0, 1)).1 +
          (fderiv ℝ P x (1, 0)).2 * (fderiv ℝ P x (0, 1)).2) ^ 2 := by ring
    _ = 1 := by rw [h1, h2, h3]; norm_num

theorem planeJacobian_pos_of_euclidean_derivative_at
    {P : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hc : IsPreconnected U)
    (hP : ∀ x ∈ U, ContDiffAt ℝ ∞ P x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    {x₀ : PolarPoint} (hx₀ : x₀ ∈ U) (hJ₀ : 0 < planeJacobian P x₀) :
    ∀ x ∈ U, 0 < planeJacobian P x := by
  have hcont : ContinuousOn (planeJacobian P) U := fun x hx =>
    (contDiffAt_planeJacobian (hP x hx)).continuousAt.continuousWithinAt
  intro x hx
  by_contra hn
  obtain ⟨z, hz, hzero⟩ := hc.intermediate_value hx hx₀ hcont ⟨le_of_not_gt hn, hJ₀.le⟩
  have hs := planeJacobian_sq_of_euclidean_derivative (hm z hz)
  rw [hzero] at hs
  norm_num at hs

/-- One actual identity germ fixes the affine motion on the whole connected open set. -/
theorem eq_id_of_euclidean_derivative_of_identity_germ
    {P : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hP : ∀ x ∈ U, ContDiffAt ℝ ∞ P x)
    (hm : ∀ x ∈ U, ∀ u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ P x u) (fderiv ℝ P x v) = coordinateEuclideanPair u v)
    {x₀ : PolarPoint} (hx₀ : x₀ ∈ U) (hfix : P =ᶠ[𝓝 x₀] id) : Set.EqOn P id U := by
  have hd₀ : fderiv ℝ P x₀ = ContinuousLinearMap.id ℝ PolarPoint := by
    simpa using hfix.fderiv_eq (𝕜 := ℝ)
  have hJ₀ : 0 < planeJacobian P x₀ := by
    simp [planeJacobian, hd₀]
  obtain ⟨c, s, b, _, hmap, hder⟩ := exists_rotation_affine_of_euclidean_derivative
    hU hc ⟨x₀, hx₀⟩ hP hm (planeJacobian_pos_of_euclidean_derivative_at hc hP hm hx₀ hJ₀)
  have hL : planeRotationLinearMap c s = ContinuousLinearMap.id ℝ PolarPoint :=
    (hder x₀ hx₀).symm.trans hd₀
  have hbase := hfix.eq_of_nhds
  rw [hmap x₀ hx₀, hL] at hbase
  have hb : b = 0 := add_left_cancel (show x₀ + b = x₀ + 0 by simpa using hbase)
  intro x hx
  simpa only [hL, ContinuousLinearMap.id_apply, hb, add_zero, id_eq] using hmap x hx

/-- Two globally smooth developments with the same actual pullback metric and the
same identity normalization on a nonempty open set are the same map. Only the first
development's inverse is needed; orientation is forced by the normalization. -/
theorem normalized_developments_unique
    (P Q : PolarPoint ≃ₜ PolarPoint)
    (hP : ContDiff ℝ ∞ (P : PolarPoint → PolarPoint))
    (hPi : ContDiff ℝ ∞ (P.symm : PolarPoint → PolarPoint))
    (hQ : ContDiff ℝ ∞ (Q : PolarPoint → PolarPoint))
    (hm : ∀ x u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ (P : PolarPoint → PolarPoint) x u)
        (fderiv ℝ (P : PolarPoint → PolarPoint) x v) =
      coordinateEuclideanPair (fderiv ℝ (Q : PolarPoint → PolarPoint) x u)
        (fderiv ℝ (Q : PolarPoint → PolarPoint) x v))
    {U : Set PolarPoint} (hU : IsOpen U) (hne : U.Nonempty)
    (hfixP : Set.EqOn P id U) (hfixQ : Set.EqOn Q id U) :
    (P : PolarPoint → PolarPoint) = (Q : PolarPoint → PolarPoint) := by
  let R : PolarPoint → PolarPoint := fun y => Q (P.symm y)
  have hRs : ContDiff ℝ ∞ R := hQ.comp hPi
  have hRm : ∀ y u v : PolarPoint,
      coordinateEuclideanPair (fderiv ℝ R y u) (fderiv ℝ R y v) = coordinateEuclideanPair u v := by
    intro y u v
    have hdP := (hP.differentiable (by simp) (P.symm y)).hasFDerivAt
    have hdPi := (hPi.differentiable (by simp) y).hasFDerivAt
    have hdQ := (hQ.differentiable (by simp) (P.symm y)).hasFDerivAt
    have hi := hdP.comp y hdPi
    have hcomp : ((P : PolarPoint → PolarPoint) ∘ (P.symm : PolarPoint → PolarPoint)) = id := by
      funext z
      simp
    rw [hcomp] at hi
    have hid := hi.fderiv
    rw [fderiv_id] at hid
    have hinv : ∀ a : PolarPoint,
        fderiv ℝ (P : PolarPoint → PolarPoint) (P.symm y)
          (fderiv ℝ (P.symm : PolarPoint → PolarPoint) y a) = a := by
      intro a
      simpa using congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L a) hid.symm
    have hRd : fderiv ℝ R y = (fderiv ℝ (Q : PolarPoint → PolarPoint) (P.symm y)).comp
        (fderiv ℝ (P.symm : PolarPoint → PolarPoint) y) := (hdQ.comp y hdPi).fderiv
    rw [hRd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hm (P.symm y), hinv, hinv]
  have hRfix : ∀ y ∈ U, R y = y := by
    intro y hy
    have hi : P.symm y = y := by
      have hh := congrArg P.symm (hfixP hy)
      simpa using hh.symm
    change Q (P.symm y) = y
    rw [hi]
    exact hfixQ hy
  obtain ⟨y₀, hy₀⟩ := hne
  have hgerm : R =ᶠ[𝓝 y₀] id := by
    filter_upwards [hU.mem_nhds hy₀] with y hy
    exact hRfix y hy
  have hR := eq_id_of_euclidean_derivative_of_identity_germ isOpen_univ isPreconnected_univ
    (fun y _ => hRs.contDiffAt) (fun y _ => hRm y) (mem_univ y₀) hgerm
  funext x
  have hx := hR (mem_univ (P x))
  simpa only [R, P.symm_apply_apply, id_eq] using hx.symm

end ContinuousFlexibility
