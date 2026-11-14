module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# One-dimensional orientation from a nonvanishing actual derivative

An oriented endpoint increment fixes the sign of a continuous nonzero
derivative throughout a preconnected domain.  The same argument applies
to either orientation of a radial piece and to a degree-one periodic lift.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n05_pos_on_of_continuous_nonzero
    {U : Set ℝ} {d : ℝ → ℝ} (hU : IsPreconnected U)
    (hd : ContinuousOn d U) (hne : ∀ x ∈ U, d x ≠ 0)
    {y : ℝ} (hy : y ∈ U) (hypos : 0 < d y) {x : ℝ} (hx : x ∈ U) :
    0 < d x := by
  by_contra hnot
  obtain ⟨z, hz, hzero⟩ := hU.intermediate_value hx hy hd
    ⟨le_of_not_gt hnot, hypos.le⟩
  exact hne z hz hzero

/-- The real orientation parameter treats both endpoint directions with the
same mean-value and intermediate-value argument. -/
theorem n05_oriented_derivative_pos
    {U : Set ℝ} {f d : ℝ → ℝ} {a b orientation : ℝ}
    (hU : IsPreconnected U) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ r ∈ Ioo a b, HasDerivAt f (d r) r)
    (hsub : Ioo a b ⊆ U) (hd : ContinuousOn d U)
    (hne : ∀ r ∈ U, d r ≠ 0)
    (hinc : 0 < orientation * (f b - f a)) {x : ℝ} (hx : x ∈ U) :
    0 < orientation * d x := by
  have ho : orientation ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hinc
    exact (lt_irrefl 0) hinc
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f d hab hf hfd
  have hcpos : 0 < orientation * d c := by
    rw [hslope]
    simpa only [mul_div_assoc] using div_pos hinc (sub_pos.mpr hab)
  exact n05_pos_on_of_continuous_nonzero hU (continuousOn_const.mul hd)
    (fun r hr => mul_ne_zero ho (hne r hr)) (hsub hc) hcpos hx

/-- A continuously differentiable degree-one lift with no zero derivative
has positive derivative everywhere. -/
theorem n05_derivative_pos_of_periodic_lift
    {f d : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hfd : ∀ θ, HasDerivAt f (d θ) θ) (hd : Continuous d)
    (hne : ∀ θ, d θ ≠ 0) (hlift : ∀ θ, f (θ + P) = f θ + P)
    (θ : ℝ) : 0 < d θ := by
  have hf : Continuous f :=
    continuous_iff_continuousAt.mpr fun t => (hfd t).continuousAt
  have hinc : 0 < (1 : ℝ) * (f (θ + P) - f θ) := by
    simpa only [hlift θ, add_sub_cancel_left, one_mul] using hP
  have hpos := n05_oriented_derivative_pos isPreconnected_univ
    (show θ < θ + P by linarith) hf.continuousOn
    (fun t _ => hfd t) (subset_univ _) hd.continuousOn
    (fun t _ => hne t) hinc (mem_univ θ)
  simpa only [one_mul] using hpos

end ContinuousFlexibility.Statements
