module

public import ContinuousFlexibility.Analysis.CanonicalBoundaryImage
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual radial value of a canonical boundary

The endpoint image theorem gives two possible radial values at every angle.
Continuity along the actual physical boundary makes the choice independent
of the angle. This supplies the constant boundary value required by the
boundary angular lift theorem, without any prescribed endpoint value of the
stored inverse chart or an additional boundary compatibility assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem continuous_two_values_constant
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Continuous f)
    (hvalues : ∀ x, f x = a ∨ f x = b) (x y : ℝ) : f x = f y := by
  have hsep (u v : ℝ) (hu : f u = a) (hv : f v = b) : False := by
    have hmid : (a + b) / 2 ∈ Icc (f u) (f v) := by
      rw [hu, hv]
      constructor <;> linarith
    obtain ⟨t, ht⟩ := intermediate_value_univ u v hf hmid
    rcases hvalues t with h | h <;> linarith
  rcases hvalues x with hx | hx <;> rcases hvalues y with hy | hy
  · exact hx.trans hy.symm
  · exact False.elim (hsep x y hx hy)
  · exact False.elim (hsep y x hy hx)
  · exact hx.trans hy.symm

/-- The actual radial image of either physical boundary is independent
of its angle. No assertion about the totalized inverse at that boundary
enters the proof. -/
theorem n06_canonicalBoundary_radial_eq_zeroAngle
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {c : ℝ}
    (hc : ∀ η : ℝ, (c, η) ∈ frontier (physicalPieceOpen S K z m)) (θ : ℝ) :
    (K.chart z m (c, θ)).1 = (K.chart z m (c, 0)).1 := by
  have hpiece := hA.referenceBounds m
  have hclosed := (hA.boundary z hz hs m).2.2.2.2.1
  have hf : Continuous (fun η : ℝ => (K.chart z m (c, η)).1) := by
    apply continuous_iff_continuousAt.mpr
    intro η
    have hline : ContinuousAt (fun t : ℝ => (c, t)) η :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact ((hclosed (c, η) (frontier_subset_closure (hc η))).1.continuousAt.comp hline).fst
  exact continuous_two_values_constant hpiece.2.1 hf
    (fun η => canonicalChart_endpoint_radial_eq_boundary hA hz hs m (c, η) (hc η)) θ 0

/-- Each entire physical boundary maps to one canonical boundary. The
two alternatives are uniform in the angle, rather than a separate choice
for every boundary point. -/
theorem n06_canonicalBoundary_radial_dichotomy
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {c : ℝ}
    (hc : ∀ η : ℝ, (c, η) ∈ frontier (physicalPieceOpen S K z m)) :
    (∀ θ : ℝ, (K.chart z m (c, θ)).1 = K.left m) ∨
      (∀ θ : ℝ, (K.chart z m (c, θ)).1 = K.right m) := by
  have he := n06_canonicalBoundary_radial_eq_zeroAngle hA hz hs m hc
  rcases canonicalChart_endpoint_radial_eq_boundary hA hz hs m (c, 0) (hc 0) with h | h
  · exact Or.inl (fun θ => (he θ).trans h)
  · exact Or.inr (fun θ => (he θ).trans h)

end ContinuousFlexibility.Analysis
