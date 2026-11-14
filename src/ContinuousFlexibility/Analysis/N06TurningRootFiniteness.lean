module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.DiscreteSubset

/-!
# Turning roots are finite on every compact interior interval

This geometric fact follows from the actual nondegeneracy clause of the
reference profile. It is separate from local finiteness of an arbitrary
canonical piece cover: that cover could still subdivide a sign interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem n06_finite_simple_zeros_on_compact {f : ℝ → ℝ} {J : Set ℝ}
    (hf : Continuous f) (hJ : IsCompact J)
    (hderiv : ∀ x ∈ J, f x = 0 → ∃ c : ℝ, HasDerivAt f c x ∧ c ≠ 0) :
    {x | x ∈ J ∧ f x = 0}.Finite := by
  have hcompact : IsCompact {x | x ∈ J ∧ f x = 0} :=
    hJ.inter_right (isClosed_eq hf continuous_const)
  apply hcompact.finite
  apply isDiscrete_iff_nhdsNE.mpr
  intro x hx
  rw [inf_principal_eq_bot]
  obtain ⟨c, hc, hc0⟩ := hderiv x hx.1 hx.2
  have havoid : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := hc.eventually_ne hc0
  filter_upwards [havoid] with y hy
  exact fun h => hy h.2

/-- The actual roots of w' cannot accumulate in the open annulus. -/
theorem n06_turningRoots_finite_on_compact {D : ReferenceData}
    (hD : RadialProfileGeometry D) {J : Set ℝ}
    (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {r | r ∈ J ∧ deriv D.w r = 0}.Finite := by
  have hw : ContDiff ℝ ∞ D.w := hD.2.2.1.1
  have hwd : ContDiff ℝ ∞ (deriv D.w) := hw.deriv'
  apply n06_finite_simple_zeros_on_compact hwd.continuous hJ
  intro r hr hzero
  exact ⟨deriv (deriv D.w) r,
    (hwd.differentiable (by simp) r).hasDerivAt,
    hD.2.2.2.2.2.2 r (hJD hr) hzero⟩

/-- The same conclusion holds directly for every chosen radial reference. -/
theorem n06_reference_turningRoots_finite_on_compact {D : ReferenceData}
    (hD : IsRadialReference D) {J : Set ℝ}
    (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {r | r ∈ J ∧ deriv D.w r = 0}.Finite := by
  obtain ⟨C, hC⟩ := hD.1
  exact n06_turningRoots_finite_on_compact hC.1 hJ hJD

end ContinuousFlexibility.Statements
