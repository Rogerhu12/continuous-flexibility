import ContinuousFlexibility.Geometry.OutwardNormalRays
import ContinuousFlexibility.Geometry.SphereCongruenceCurvature
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

/-!
# Identification of the bounded inside and its outward unit normal

Connected unbounded exteriors and a common actual frontier identify two bounded
open inside regions. At a genuine immersed sphere, two outward unit normals for
the same region are equal as full functions. This allows the derivative and the
Weingarten shape operator to be compared after the actual normal is identified.
-/

noncomputable section

namespace ContinuousFlexibility

open Set
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false

/-- A bounded open region with the same frontier is contained in the region
whose exterior is preconnected and unbounded. -/
theorem bounded_region_subset_of_frontier_eq
    {X : Type*} [TopologicalSpace X] [Bornology X] {Ω U : Set X}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hEc : IsPreconnected (closure Ω)ᶜ) (hEu : ¬ Bornology.IsBounded (closure Ω)ᶜ)
    (hfront : frontier Ω = frontier U) : U ⊆ Ω := by
  have hdisj : Disjoint U (closure U)ᶜ :=
    Set.disjoint_left.mpr (fun _ hx hxc => hxc (subset_closure hx))
  have hcover : (closure Ω)ᶜ ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · right
      intro hxcl
      have hxf : x ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hxcl, hxU⟩
      rw [← hfront] at hxf
      exact hx (frontier_subset_closure hxf)
  have hex : (closure Ω)ᶜ ⊆ (closure U)ᶜ := by
    rcases hEc.subset_or_subset hU isClosed_closure.isOpen_compl hdisj hcover with h | h
    · exact False.elim (hEu (hUb.subset h))
    · exact h
  intro x hxU
  by_contra hxΩ
  by_cases hxcl : x ∈ closure Ω
  · have hxf : x ∈ frontier Ω := by
      rw [hΩ.frontier_eq]
      exact ⟨hxcl, hxΩ⟩
    rw [hfront, hU.frontier_eq] at hxf
    exact hxf.2 hxU
  · exact (hex hxcl) (subset_closure hxU)

/-- The bounded inside is unique when both actual exteriors are preconnected
and unbounded. No separation theorem or extra interior hypothesis is needed. -/
theorem bounded_regions_eq_of_frontier_eq
    {X : Type*} [TopologicalSpace X] [Bornology X] {Ω U : Set X}
    (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hΩb : Bornology.IsBounded Ω) (hUb : Bornology.IsBounded U)
    (hΩc : IsPreconnected (closure Ω)ᶜ) (hUc : IsPreconnected (closure U)ᶜ)
    (hΩu : ¬ Bornology.IsBounded (closure Ω)ᶜ)
    (hUu : ¬ Bornology.IsBounded (closure U)ᶜ)
    (hfront : frontier Ω = frontier U) : Ω = U :=
  Set.Subset.antisymm
    (bounded_region_subset_of_frontier_eq hU hΩ hΩb hUc hUu hfront.symm)
    (bounded_region_subset_of_frontier_eq hΩ hU hUb hΩc hΩu hfront)

local notation "SpherePoint" => {v : E3 // v ∈ Metric.sphere (0 : E3) 1}

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

/-- Both normals are transported through the same genuine sphere chart.
Outwardness for the same actual region excludes the negative alternative. -/
theorem sphere_outward_normals_eq
    {F N M : SpherePoint → E3} {Ω : Set E3}
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) F x))
    (hN : ∀ x, ‖N x‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (N x) = 0)
    (hM : ∀ x, ‖M x‖ = 1 ∧ ∀ v : TangentSpace (𝓡 2) x,
      inner ℝ (mvfderiv (𝓡 2) F x v) (M x) = 0)
    (houtN : ∀ x, PointsOutwardFrom Ω (F x) (N x))
    (houtM : ∀ x, PointsOutwardFrom Ω (F x) (M x)) : M = N := by
  funext x
  have hn := isUnitSurfaceNormal_sphereCanonicalSurfaceChart hF hN x
    (sphereCanonicalCoordinates x x)
  have hm := isUnitSurfaceNormal_sphereCanonicalSurfaceChart hF hM x
    (sphereCanonicalCoordinates x x)
  rw [sphereCanonicalCoordinates_left_inv] at hn hm
  exact (houtN x).eq_of_eq_or_eq_neg (houtM x)
    (hn.eq_or_eq_neg hm (sphereCanonicalSurfaceChart_fderiv_injective hF hi x _))

end ContinuousFlexibility

