module

public import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-!
# Linearity of the actual signed potential relation

The potential coordinate is multiplication by the actual radial
coefficient in μ_D. Its graph is a linear subspace, including for
negative retained wells. No bound or positivity assumption replaces
this constitutive relation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped InnerProductSpace

theorem innerRadialPotentialClass_zero (D : ReferenceData) (j a b : ℝ) :
    InnerRadialPotentialClass D j a b 0 0 := by
  filter_upwards [Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr
  by_cases hmem : r ∈ Ioo a b
  · simp only [indicator_of_mem hmem, hr, Pi.zero_apply, mul_zero]
  · simp only [indicator_of_notMem hmem, hr, Pi.zero_apply]

theorem InnerRadialPotentialClass.add {D : ReferenceData} {j a b : ℝ}
    {u v u' v' : RadialModeL2 D}
    (h : InnerRadialPotentialClass D j a b u v)
    (h' : InnerRadialPotentialClass D j a b u' v') :
    InnerRadialPotentialClass D j a b (u + u') (v + v') := by
  filter_upwards [h, h', Lp.coeFn_add u u', Lp.coeFn_add v v'] with r hr hr' hu hv
  rw [hv, Pi.add_apply, hr, hr']
  by_cases hmem : r ∈ Ioo a b
  · simp only [indicator_of_mem hmem, hu, Pi.add_apply, mul_add]
  · simp only [indicator_of_notMem hmem, zero_add]

theorem InnerRadialPotentialClass.smul {D : ReferenceData} {j a b : ℝ}
    {u v : RadialModeL2 D} (h : InnerRadialPotentialClass D j a b u v) (c : ℝ) :
    InnerRadialPotentialClass D j a b (c • u) (c • v) := by
  filter_upwards [h, Lp.coeFn_smul c u, Lp.coeFn_smul c v] with r hr hu hv
  rw [hv, Pi.smul_apply, smul_eq_mul, hr]
  by_cases hmem : r ∈ Ioo a b
  · simp only [indicator_of_mem hmem, hu, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [indicator_of_notMem hmem, mul_zero]

/-- A genuine potential product vanishes when its value coordinate does. -/
theorem InnerRadialPotentialClass.eq_zero_of_value_eq_zero
    {D : ReferenceData} {j a b : ℝ} {u v : RadialModeL2 D}
    (h : InnerRadialPotentialClass D j a b u v) (hu : u = 0) : v = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  rw [hu] at h
  filter_upwards [h, Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr hz
  by_cases hmem : r ∈ Ioo a b
  · simpa only [indicator_of_mem hmem, hz, Pi.zero_apply, mul_zero] using hr
  · simpa only [indicator_of_notMem hmem, Pi.zero_apply] using hr

/-- The actual real signed potential contributes a symmetric pairing. -/
theorem InnerRadialPotentialClass.inner_symm
    {D : ReferenceData} {j a b : ℝ} {u v u' v' : RadialModeL2 D}
    (h : InnerRadialPotentialClass D j a b u v)
    (h' : InnerRadialPotentialClass D j a b u' v') :
    ⟪v, u'⟫_ℝ = ⟪v', u⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h, h'] with r hr hr'
  rw [hr, hr']
  by_cases hmem : r ∈ Ioo a b
  · simp only [indicator_of_mem hmem, RCLike.inner_apply, conj_trivial]
    ring
  · simp only [indicator_of_notMem hmem, inner_zero_left]

/-- The genuine physical multiplication graph. -/
def innerRadialPotentialGraph (D : ReferenceData) (j a b : ℝ) :
    Submodule ℝ (RadialModeL2 D × RadialModeL2 D) where
  carrier := {z | InnerRadialPotentialClass D j a b z.1 z.2}
  zero_mem' := innerRadialPotentialClass_zero D j a b
  add_mem' := by
    intro x y hx hy
    exact hx.add hy
  smul_mem' := by
    intro c x hx
    exact hx.smul c

end ContinuousFlexibility.Radial
