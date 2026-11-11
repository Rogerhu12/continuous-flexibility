import ContinuousFlexibility.Radial.R07OutgoingFamily
import ContinuousFlexibility.Radial.R07NaturalTailScale

/-!
# Exact outgoing-state invariance under a scalar tail change

The normalized deep Cauchy data determine the finite transported state.
When the coefficient is multiplied by one positive scalar on that interval,
both actual solutions satisfy the same homogeneous equation. Finite radial
uniqueness then gives equality of the outgoing states at the matching seam.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem cauchyData_eq_of_eqOn_uIcc {u v : ℝ → ℝ} {e f : ℝ} (hne : e ≠ f)
    (hu : DifferentiableAt ℝ u e) (hv : DifferentiableAt ℝ v e)
    (heq : EqOn u v (uIcc e f)) : u e = v e ∧ deriv u e = deriv v e := by
  have he : u =ᶠ[𝓝[uIcc e f] e] v := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq hx
  have hvalue : u e = v e := heq left_mem_uIcc
  have hud : HasDerivWithinAt u (deriv u e) (uIcc e f) e := hu.hasDerivAt.hasDerivWithinAt
  have hvd : HasDerivWithinAt v (deriv v e) (uIcc e f) e := hv.hasDerivAt.hasDerivWithinAt
  have huniq := uniqueDiffOn_uIcc hne e left_mem_uIcc
  exact ⟨hvalue, (hud.derivWithin huniq).symm.trans
    ((he.derivWithin_eq hvalue).trans (hvd.derivWithin huniq))⟩

/-- Equality of normalized deep Cauchy data survives transport back through
an interval on which the actual profiles differ by one positive scalar. -/
theorem r07OutgoingState_eq_of_scaled_profile {D E : ReferenceData}
    (hD : RadialProfileGeometry D) (hE : RadialProfileGeometry E)
    {side : Bool} {j : ℕ} {e f scale : ℝ}
    (heD : e ∈ radialCore D) (hfD : f ∈ radialCore D)
    (heE : e ∈ radialCore E) (hfE : f ∈ radialCore E)
    (hef : if side then e < f else f < e) (hs : 0 < scale)
    (hw : ∀ r ∈ uIcc e f, E.w =ᶠ[𝓝 r] fun x => scale * D.w x)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hNu : RadialNaturalTail D side j e u) (hNv : RadialNaturalTail E side j e v)
    (hvalue : v f = u f) (hslope : deriv v f = deriv u f) :
    r07OutgoingState j e v = r07OutgoingState j e u := by
  have hne : e ≠ f := by
    cases side
    · exact (ne_of_lt hef).symm
    · exact ne_of_lt hef
  have huEq := radialNaturalTail_zero_uIcc hD heD hfD hef hu hNu
  have hvEqE := radialNaturalTail_zero_uIcc hE heE hfE hef hv hNv
  have hvEq (r : ℝ) (hr : r ∈ uIcc e f) : radialJacobi ((j : ℝ) ^ 2) D.w v r = 0 := by
    have h := radialJacobi_profile_scale_germ (hw r hr) ((j : ℝ) ^ 2) v
    have hz : scale * radialJacobi ((j : ℝ) ^ 2) D.w v r = 0 := h.symm.trans (hvEqE r hr)
    exact (mul_eq_zero.mp hz).resolve_left hs.ne'
  have heq : EqOn v u (uIcc e f) := radialHomogeneous_eqOn_Icc hD
    (lt_min heD.1 hfD.1) (min_le_max e f) (max_lt heD.2 hfD.2)
    (show f ∈ Icc (min e f) (max e f) from right_mem_uIcc) hv hu hvEq huEq hvalue hslope
  obtain ⟨h₀, h₁⟩ := cauchyData_eq_of_eqOn_uIcc hne
    (hv.differentiable (by simp) e) (hu.differentiable (by simp) e) heq
  simp only [r07OutgoingState, h₀, h₁]

end ContinuousFlexibility.Radial
