module

public import ContinuousFlexibility.Geometry.GlobalInverse
public import ContinuousFlexibility.Geometry.LocalInverse
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Global inversion of a planar local development

Properness turns a local homeomorphism of the plane into a covering map.
The identity of the simply connected plane has an actual covering lift;
uniqueness of lifts then proves that this lift is a two-sided global
inverse. An identity-outside-compact development consequently is a global
homeomorphism and preserves every region outside which it is fixed.

This is a statement about the whole coordinate plane, not an annulus.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility

open Set Function
open scoped ContDiff

theorem finite_fiber_of_proper_localHomeomorph {P : PolarPoint → PolarPoint}
    (hproper : IsProperMap P) (hlocal : IsLocalHomeomorph P) (y : PolarPoint) :
    (P ⁻¹' {y}).Finite := by
  have hd : IsDiscrete (P ⁻¹' {y}) :=
    IsDiscrete.of_openPartialHomeomorph P subset_rfl (fun x _ => by
      obtain ⟨e, hx, he⟩ := hlocal x
      exact ⟨e, hx, he.symm⟩)
  exact (hproper.isCompact_preimage isCompact_singleton).finite hd

theorem isCoveringMap_of_proper_localHomeomorph {P : PolarPoint → PolarPoint}
    (hproper : IsProperMap P) (hlocal : IsLocalHomeomorph P) : IsCoveringMap P := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y _
    exact finite_fiber_of_proper_localHomeomorph hproper hlocal y
  · exact hlocal.isLocalHomeomorphOn

/-- Lifting the identity of the plane gives an actual global inverse. -/
theorem exists_globalInverse_of_plane_covering {P : PolarPoint → PolarPoint}
    (hcover : IsCoveringMap P) :
    ∃ Q : PolarPoint → PolarPoint,
      Continuous Q ∧ LeftInverse Q P ∧ RightInverse Q P := by
  obtain ⟨Q, hQ, -⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id PolarPoint) (P 0) 0 rfl
  have hright : RightInverse (Q : PolarPoint → PolarPoint) P := by
    intro y
    exact congrFun hQ.2 y
  have heq : (Q : PolarPoint → PolarPoint) ∘ P = id := by
    apply hcover.eq_of_comp_eq (Q.continuous.comp hcover.continuous) continuous_id
      (a := 0)
    · funext y
      exact hright (P y)
    · exact hQ.1
  exact ⟨Q, Q.continuous, fun y => congrFun heq y, hright⟩

theorem isHomeomorph_of_plane_covering {P : PolarPoint → PolarPoint}
    (hcover : IsCoveringMap P) : IsHomeomorph P := by
  obtain ⟨Q, -, hleft, hright⟩ := exists_globalInverse_of_plane_covering hcover
  exact ⟨hcover.continuous, hcover.isOpenMap, ⟨hleft.injective, hright.surjective⟩⟩

theorem isHomeomorph_of_proper_localHomeomorph_plane {P : PolarPoint → PolarPoint}
    (hproper : IsProperMap P) (hlocal : IsLocalHomeomorph P) : IsHomeomorph P :=
  isHomeomorph_of_plane_covering (isCoveringMap_of_proper_localHomeomorph hproper hlocal)

theorem isHomeomorph_of_eq_id_outside_compact {P : PolarPoint → PolarPoint}
    {K : Set PolarPoint} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → P x = x)
    (hlocal : IsLocalHomeomorph P) : IsHomeomorph P :=
  isHomeomorph_of_proper_localHomeomorph_plane
    (isProperMap_of_eq_id_outside_compact hlocal.continuous hK hfix) hlocal

theorem exists_homeomorph_of_eq_id_outside_compact {P : PolarPoint → PolarPoint}
    {K : Set PolarPoint} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → P x = x)
    (hlocal : IsLocalHomeomorph P) :
    ∃ e : PolarPoint ≃ₜ PolarPoint, (e : PolarPoint → PolarPoint) = P := by
  have hh := isHomeomorph_of_eq_id_outside_compact hK hfix hlocal
  exact ⟨IsHomeomorph.homeomorph P hh, rfl⟩

theorem image_compact_region_eq_self_of_localHomeomorph
    {P : PolarPoint → PolarPoint} {K : Set PolarPoint}
    (hK : IsCompact K) (hfix : ∀ x, x ∉ K → P x = x)
    (hlocal : IsLocalHomeomorph P) : P '' K = K :=
  image_eq_self_of_bijective_eq_id_outside
    (isHomeomorph_of_eq_id_outside_compact hK hfix hlocal).bijective hfix

/-- The inverse of a globally smooth planar homeomorphism is smooth when its derivative is
invertible at every point. This applies the actual local inverse regularity theorem. -/
theorem contDiffAt_homeomorph_symm_of_fderiv_bijective
    (e : PolarPoint ≃ₜ PolarPoint)
    (he : ∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x)
    (hbij : ∀ x, Bijective (fderiv ℝ (e : PolarPoint → PolarPoint) x)) (y : PolarPoint) :
    ContDiffAt ℝ ∞ (e.symm : PolarPoint → PolarPoint) y := by
  let A := planeLinearEquivOfBijective
    (fderiv ℝ (e : PolarPoint → PolarPoint) (e.symm y)) (hbij (e.symm y))
  have hA : (A : PolarPoint →L[ℝ] PolarPoint) =
      fderiv ℝ (e : PolarPoint → PolarPoint) (e.symm y) :=
    planeLinearEquivOfBijective_coe _ _
  have hd : HasFDerivAt (e : PolarPoint → PolarPoint)
      (A : PolarPoint →L[ℝ] PolarPoint) (e.symm y) := by
    rw [hA]
    exact ((he (e.symm y)).differentiableAt (by simp)).hasFDerivAt
  exact e.toOpenPartialHomeomorph.contDiffAt_symm (by trivial) hd (he (e.symm y))

/-- A smooth planar map with everywhere invertible derivative and identity outside a compact
set is a global smooth homeomorphism in both directions. -/
theorem exists_smooth_homeomorph_of_eq_id_outside_compact
    {P : PolarPoint → PolarPoint} {K : Set PolarPoint}
    (hK : IsCompact K) (hfix : ∀ x, x ∉ K → P x = x)
    (hP : ∀ x, ContDiffAt ℝ ∞ P x)
    (hbij : ∀ x, Bijective (fderiv ℝ P x)) :
    ∃ e : PolarPoint ≃ₜ PolarPoint, (e : PolarPoint → PolarPoint) = P ∧
      (∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x) ∧
        ∀ y, ContDiffAt ℝ ∞ (e.symm : PolarPoint → PolarPoint) y := by
  have hlocal : IsLocalHomeomorph P := by
    intro x
    obtain ⟨e, he, hx, -, -⟩ := exists_localInverse_of_fderiv_bijective
      (hP x) (by simp) (hbij x)
    exact ⟨e, hx, he.symm⟩
  let e := IsHomeomorph.homeomorph P
    (isHomeomorph_of_eq_id_outside_compact hK hfix hlocal)
  have he : (e : PolarPoint → PolarPoint) = P := rfl
  have heSmooth : ∀ x, ContDiffAt ℝ ∞ (e : PolarPoint → PolarPoint) x := by
    simpa only [he] using hP
  have heBij : ∀ x, Bijective (fderiv ℝ (e : PolarPoint → PolarPoint) x) := by
    simpa only [he] using hbij
  exact ⟨e, he, heSmooth, contDiffAt_homeomorph_symm_of_fderiv_bijective e heSmooth heBij⟩

end ContinuousFlexibility
