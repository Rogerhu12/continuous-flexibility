import ContinuousFlexibility.Scalar.Coordinates
import ContinuousFlexibility.Scalar.Positivity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Local inversion of a planar development

A derivative whose coordinate Euclidean quadratic form equals a positive
remainder quadratic form is injective, and hence bijective in dimension two.
The actual inverse function theorem then supplies an open partial
homeomorphism and a smooth local inverse. The coordinate square sum is never
replaced by the default product norm on `PolarPoint`.
-/

noncomputable section

namespace ContinuousFlexibility

open scoped ContDiff

variable {r E k p : ℝ}

theorem linear_injective_of_remainder_metric (L : PolarPoint →L[ℝ] PolarPoint)
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (L v).1 ^ 2 + (L v).2 ^ 2 = remainderQuadratic r E k p v.1 v.2) :
    Function.Injective L := by
  have hpositive := remainderPositive_of_discriminant_pos hr hE hD
  have hker : ∀ v : PolarPoint, L v = 0 → v = 0 := by
    intro v hzero
    by_contra hv
    have hxy : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
      by_cases h1 : v.1 = 0
      · right
        intro h2
        exact hv (Prod.ext h1 h2)
      · exact Or.inl h1
    have hpos := hpositive v.1 v.2 hxy
    have hq : remainderQuadratic r E k p v.1 v.2 = 0 := by
      simpa only [hzero, Prod.fst_zero, Prod.snd_zero, zero_pow (by decide : 2 ≠ 0),
        zero_add] using (hmetric v).symm
    exact hpos.ne' hq
  intro u v huv
  apply sub_eq_zero.mp
  apply hker (u - v)
  rw [map_sub, huv, sub_self]

theorem linear_bijective_of_remainder_metric (L : PolarPoint →L[ℝ] PolarPoint)
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (L v).1 ^ 2 + (L v).2 ^ 2 = remainderQuadratic r E k p v.1 v.2) :
    Function.Bijective L := by
  have hinj := linear_injective_of_remainder_metric L hr hE hD hmetric
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩

/-- A bijective planar continuous linear map is a continuous linear equivalence. -/
def planeLinearEquivOfBijective (L : PolarPoint →L[ℝ] PolarPoint)
    (hL : Function.Bijective L) : PolarPoint ≃L[ℝ] PolarPoint :=
  (LinearEquiv.ofBijective L.toLinearMap hL).toContinuousLinearEquiv

theorem planeLinearEquivOfBijective_coe (L : PolarPoint →L[ℝ] PolarPoint)
    (hL : Function.Bijective L) :
    (planeLinearEquivOfBijective L hL : PolarPoint →L[ℝ] PolarPoint) = L := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem fderiv_injective_of_remainder_metric {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic r E k p v.1 v.2) :
    Function.Injective (fderiv ℝ P x) :=
  linear_injective_of_remainder_metric (fderiv ℝ P x) hr hE hD hmetric

theorem fderiv_bijective_of_remainder_metric {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic r E k p v.1 v.2) :
    Function.Bijective (fderiv ℝ P x) :=
  linear_bijective_of_remainder_metric (fderiv ℝ P x) hr hE hD hmetric

theorem exists_fderiv_linearEquiv_of_remainder_metric
    {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic r E k p v.1 v.2) :
    ∃ A : PolarPoint ≃L[ℝ] PolarPoint,
      (A : PolarPoint →L[ℝ] PolarPoint) = fderiv ℝ P x := by
  let hL := fderiv_bijective_of_remainder_metric hr hE hD hmetric
  exact ⟨planeLinearEquivOfBijective (fderiv ℝ P x) hL,
    planeLinearEquivOfBijective_coe (fderiv ℝ P x) hL⟩

/-- The genuine inverse function theorem, for any positive differentiability order. -/
theorem exists_localInverse_of_fderiv_bijective
    {P : PolarPoint → PolarPoint} {x : PolarPoint} {n : ℕ∞ω}
    (hP : ContDiffAt ℝ n P x) (hn : n ≠ 0)
    (hbij : Function.Bijective (fderiv ℝ P x)) :
    ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
      (e : PolarPoint → PolarPoint) = P ∧ x ∈ e.source ∧ P x ∈ e.target ∧
        ContDiffAt ℝ n e.symm (P x) := by
  let A := planeLinearEquivOfBijective (fderiv ℝ P x) hbij
  have hA : (A : PolarPoint →L[ℝ] PolarPoint) = fderiv ℝ P x :=
    planeLinearEquivOfBijective_coe (fderiv ℝ P x) hbij
  have hd : HasFDerivAt P (A : PolarPoint →L[ℝ] PolarPoint) x := by
    rw [hA]
    exact (hP.differentiableAt hn).hasFDerivAt
  let e := hP.toOpenPartialHomeomorph P hd hn
  refine ⟨e, rfl, hP.mem_toOpenPartialHomeomorph_source hd hn,
    hP.image_mem_toOpenPartialHomeomorph_target hd hn, ?_⟩
  change ContDiffAt ℝ n (hP.localInverse hd hn) (P x)
  exact hP.to_localInverse hd hn

/-- Positive remainder metric gives a local inverse whose regularity matches `P`. -/
theorem exists_localInverse_of_remainder_metric
    {P : PolarPoint → PolarPoint} {x : PolarPoint} {n : ℕ∞ω}
    (hP : ContDiffAt ℝ n P x) (hn : n ≠ 0)
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic r E k p v.1 v.2) :
    ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
      (e : PolarPoint → PolarPoint) = P ∧ x ∈ e.source ∧ P x ∈ e.target ∧
        ContDiffAt ℝ n e.symm (P x) :=
  exists_localInverse_of_fderiv_bijective hP hn
    (fderiv_bijective_of_remainder_metric hr hE hD hmetric)

/-- The smooth case uses `∞`, not the stronger analytic order `ω`. -/
theorem exists_smooth_localInverse_of_remainder_metric
    {P : PolarPoint → PolarPoint} {x : PolarPoint}
    (hP : ContDiffAt ℝ ∞ P x)
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic r E k p v.1 v.2) :
    ∃ e : OpenPartialHomeomorph PolarPoint PolarPoint,
      (e : PolarPoint → PolarPoint) = P ∧ x ∈ e.source ∧ P x ∈ e.target ∧
        ContDiffAt ℝ ∞ e.symm (P x) :=
  exists_localInverse_of_remainder_metric hP (by simp) hr hE hD hmetric

theorem exists_open_injOn_of_remainder_metric
    {P : PolarPoint → PolarPoint} {x : PolarPoint} {n : ℕ∞ω}
    (hP : ContDiffAt ℝ n P x) (hn : n ≠ 0)
    (hr : 0 < r) (hE : 0 < E) (hD : 0 < heightDiscriminant E k p)
    (hmetric : ∀ v : PolarPoint,
      (fderiv ℝ P x v).1 ^ 2 + (fderiv ℝ P x v).2 ^ 2 =
        remainderQuadratic r E k p v.1 v.2) :
    ∃ U : Set PolarPoint, IsOpen U ∧ x ∈ U ∧ Set.InjOn P U := by
  obtain ⟨e, he, hx, -, -⟩ := exists_localInverse_of_remainder_metric
    hP hn hr hE hD hmetric
  refine ⟨e.source, e.open_source, hx, ?_⟩
  simpa only [he] using e.injOn

end ContinuousFlexibility
