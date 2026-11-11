import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper planar developments

A continuous planar map which equals the identity outside a compact set is
proper. This is the first global reconstruction step of Section 2. It does
not assume that an annulus is convex or that its connection has a global
real-valued primitive.
-/

noncomputable section

namespace ContinuousFlexibility

open Set

theorem isCompact_preimage_of_eq_id_outside_compact
    {P : PolarPoint → PolarPoint} {K S : Set PolarPoint}
    (hP : Continuous P) (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → P x = x) (hS : IsCompact S) :
    IsCompact (P ⁻¹' S) := by
  apply (hK.union hS).of_isClosed_subset (hS.isClosed.preimage hP)
  intro x hx
  by_cases hxK : x ∈ K
  · exact Or.inl hxK
  · right
    change P x ∈ S at hx
    rw [hfix x hxK] at hx
    exact hx

theorem isProperMap_of_eq_id_outside_compact
    {P : PolarPoint → PolarPoint} {K : Set PolarPoint}
    (hP : Continuous P) (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → P x = x) : IsProperMap P := by
  apply isProperMap_iff_isCompact_preimage.mpr
  exact ⟨hP, fun _ hS => isCompact_preimage_of_eq_id_outside_compact hP hK hfix hS⟩

theorem isClosedMap_of_eq_id_outside_compact
    {P : PolarPoint → PolarPoint} {K : Set PolarPoint}
    (hP : Continuous P) (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → P x = x) : IsClosedMap P :=
  (isProperMap_of_eq_id_outside_compact hP hK hfix).isClosedMap

theorem isCompact_fiber_of_eq_id_outside_compact
    {P : PolarPoint → PolarPoint} {K : Set PolarPoint}
    (hP : Continuous P) (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → P x = x) (y : PolarPoint) :
    IsCompact (P ⁻¹' {y}) :=
  (isProperMap_of_eq_id_outside_compact hP hK hfix).isCompact_preimage isCompact_singleton

/-- A global bijection fixed outside a region maps that region onto itself. -/
theorem image_eq_self_of_bijective_eq_id_outside
    {P : PolarPoint → PolarPoint} {S : Set PolarPoint}
    (hbij : Function.Bijective P) (hfix : ∀ x, x ∉ S → P x = x) : P '' S = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_contra hPx
    have heq : P (P x) = P x := hfix (P x) hPx
    have hpoint : P x = x := hbij.injective heq
    apply hPx
    rw [hpoint]
    exact hx
  · intro hy
    obtain ⟨x, hxy⟩ := hbij.surjective y
    refine ⟨x, ?_, hxy⟩
    by_contra hx
    have hpoint : x = y := (hfix x hx).symm.trans hxy
    apply hx
    rw [hpoint]
    exact hy

end ContinuousFlexibility
