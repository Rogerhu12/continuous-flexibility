import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields
import ContinuousFlexibility.Analysis.PositiveReferenceCylinder

/-!
# Positive charts with distinct physical and canonical intervals

This is a property of the displayed chart, inverse and height. It keeps
the physical and canonical endpoints separate and has no identity
normalization in the middle. The existing scalar reference interpolation
supplies it directly, in particular for canonical interval (0, 1).
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

structure PositiveChartRangeGeometry
    (F G : PolarPoint → PolarPoint) (h : PolarPoint → ℝ)
    (l r u v : ℝ) : Prop where
  chart_smooth : ContDiff ℝ ∞ F
  inverse_smooth : ContDiff ℝ ∞ G
  height_smooth : ContDiff ℝ ∞ h
  height_positive : ∀ p, 0 < h p
  left_inverse : Function.LeftInverse G F
  right_inverse : Function.RightInverse G F
  jacobian_positive : ∀ p, 0 < planeJacobian F p
  maps_open : MapsTo F (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo u v ×ˢ (univ : Set ℝ))
  inverse_maps_open : MapsTo G (Ioo u v ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  maps_closed : MapsTo F (Icc l r ×ˢ (univ : Set ℝ)) (Icc u v ×ˢ (univ : Set ℝ))
  inverse_maps_closed : MapsTo G (Icc u v ×ˢ (univ : Set ℝ)) (Icc l r ×ˢ (univ : Set ℝ))
  period_add : ∀ p, F (p + (0, Real.pi)) = F p + (0, Real.pi)
  inverse_period_add : ∀ p, G (p + (0, Real.pi)) = G p + (0, Real.pi)
  height_period : ∀ p, h (p + (0, Real.pi)) = h p
  reflect : ∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2)
  inverse_reflect : ∀ p, G (p.1, -p.2) = ((G p).1, -(G p).2)
  height_even : ∀ p, h (p.1, -p.2) = h p

theorem PositiveChartRangeGeometry.bijOn
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r u v : ℝ}
    (H : PositiveChartRangeGeometry F G h l r u v) :
    BijOn F (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo u v ×ˢ (univ : Set ℝ)) :=
  ⟨H.maps_open, H.left_inverse.injective.injOn,
    fun p hp => ⟨G p, H.inverse_maps_open hp, H.right_inverse p⟩⟩

theorem PositiveChartRangeGeometry.inverse_germs
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r u v : ℝ}
    (H : PositiveChartRangeGeometry F G h l r u v) (p : PolarPoint) :
    CanonicalBoundaryInverseGerm F G p ∧ CanonicalBoundaryInverseGerm G F p := by
  have hi : F ∘ G =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) :=
    Filter.Eventually.of_forall H.right_inverse
  have hprod := planeJacobian_inverse_mul_of_germ
    (H.inverse_smooth.differentiable (by simp) p)
    (H.chart_smooth.differentiable (by simp) (G p)) hi
  have hJG : planeJacobian G p ≠ 0 := by
    intro he
    rw [he, mul_zero] at hprod
    exact zero_ne_one hprod
  exact ⟨canonicalBoundaryInverseGerm_of_global_leftInverse
      H.chart_smooth.contDiffAt (H.jacobian_positive p).ne' H.left_inverse,
    canonicalBoundaryInverseGerm_of_global_leftInverse
      H.inverse_smooth.contDiffAt hJG H.right_inverse⟩

theorem PositiveChartRangeGeometry.boundary_fields
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r u v : ℝ}
    (H : PositiveChartRangeGeometry F G h l r u v) (hlr : l < r) :
    MapsTo F (closure (Ioo l r ×ˢ (univ : Set ℝ))) (Icc u v ×ˢ (univ : Set ℝ)) ∧
    MapsTo G (Icc u v ×ˢ (univ : Set ℝ)) (closure (Ioo l r ×ˢ (univ : Set ℝ))) ∧
    (∀ p ∈ closure (Ioo l r ×ˢ (univ : Set ℝ)), G (F p) = p) ∧
    (∀ p ∈ Icc u v ×ˢ (univ : Set ℝ), F (G p) = p) ∧
    (∀ p ∈ closure (Ioo l r ×ˢ (univ : Set ℝ)),
      ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧
      planeJacobian F p ≠ 0 ∧ 0 < h p) ∧
    (∀ p ∈ frontier (Ioo l r ×ˢ (univ : Set ℝ)),
      CanonicalBoundaryInverseGerm F G p) := by
  have hclosed : closure (Ioo l r ×ˢ (univ : Set ℝ)) =
      Icc l r ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_Ioo hlr.ne, closure_univ]
  rw [hclosed]
  exact ⟨H.maps_closed, H.inverse_maps_closed, fun p _ => H.left_inverse p,
    fun p _ => H.right_inverse p,
    fun p _ => ⟨H.chart_smooth.contDiffAt, H.height_smooth.contDiffAt,
      (H.jacobian_positive p).ne', H.height_positive p⟩,
    fun p _ => (H.inverse_germs p).1⟩

theorem PositiveChartRangeGeometry.jacobian_even
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r u v : ℝ}
    (H : PositiveChartRangeGeometry F G h l r u v) (p : PolarPoint) :
    planeJacobian F (p.1, -p.2) = planeJacobian F p :=
  planeJacobian_even_of_angle_reflection
    (H.chart_smooth.differentiable (by simp)) H.reflect p

/-- The scalar outputs of the existing reference factory give the
two-dimensional range certificate. No endpoint range is silently
identified with the physical interval. -/
theorem positiveReferenceCylinder_rangeGeometry
    {Y H : ℝ → ℝ} {l r u v : ℝ}
    (hY : ContDiff ℝ ∞ Y) (hYpos : ∀ x, 0 < deriv Y x)
    (hYbij : Function.Bijective Y) (hYinv : ContDiff ℝ ∞ (Function.invFun Y))
    (hH : ContDiff ℝ ∞ H) (hHpos : ∀ x, 0 < H x)
    (hleft : Y l = u) (hright : Y r = v) :
    PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r u v := by
  have hmono : StrictMono Y := strictMono_of_deriv_pos hYpos
  have hmonoInv : StrictMono (Function.invFun Y) := by
    intro x y hxy
    apply hmono.lt_iff_lt.mp
    simpa only [Function.rightInverse_invFun hYbij.2] using hxy
  have hleftInv : Function.invFun Y u = l := by
    rw [← hleft]
    exact Function.leftInverse_invFun hYbij.1 l
  have hrightInv : Function.invFun Y v = r := by
    rw [← hright]
    exact Function.leftInverse_invFun hYbij.1 r
  refine {
    chart_smooth := contDiff_positiveReferenceCylinderChart hY
    inverse_smooth := contDiff_positiveReferenceCylinderInverse hYinv
    height_smooth := hH.comp contDiff_fst
    height_positive := fun p => hHpos p.1
    left_inverse := positiveReferenceCylinder_leftInverse hYbij.1
    right_inverse := positiveReferenceCylinder_rightInverse hYbij.2
    jacobian_positive := ?_
    maps_open := ?_
    inverse_maps_open := ?_
    maps_closed := ?_
    inverse_maps_closed := ?_
    period_add := ?_
    inverse_period_add := ?_
    height_period := ?_
    reflect := ?_
    inverse_reflect := ?_
    height_even := ?_ }
  · intro p
    rw [planeJacobian_positiveReferenceCylinderChart (hY.differentiable (by simp) p.1)]
    exact hYpos p.1
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [hleft] using hmono hp.1.1
    · simpa only [hright] using hmono hp.1.2
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [hleftInv] using hmonoInv hp.1.1
    · simpa only [hrightInv] using hmonoInv hp.1.2
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [hleft] using hmono.monotone hp.1.1
    · simpa only [hright] using hmono.monotone hp.1.2
  · intro p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [hleftInv] using hmonoInv.monotone hp.1.1
    · simpa only [hrightInv] using hmonoInv.monotone hp.1.2
  · rintro ⟨x, θ⟩
    simp only [positiveReferenceCylinderChart, Prod.mk_add_mk, add_zero]
  · rintro ⟨x, θ⟩
    simp only [positiveReferenceCylinderInverse, Prod.mk_add_mk, add_zero]
  · rintro ⟨x, θ⟩
    simp only [Prod.mk_add_mk, add_zero]
  · rintro ⟨x, θ⟩
    rfl
  · rintro ⟨x, θ⟩
    rfl
  · rintro ⟨x, θ⟩
    rfl

end ContinuousFlexibility.Analysis
