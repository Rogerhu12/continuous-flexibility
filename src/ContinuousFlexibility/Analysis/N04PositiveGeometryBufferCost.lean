import ContinuousFlexibility.Analysis.EndpointTransportGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

/-!
# A necessary cost of freezing a positive transport on a middle interval

An angular displacement at an endpoint must be joined to zero at the end
of the frozen middle. The mean-value theorem therefore charges the
reciprocal width of this transition, in the coordinate in which the jets
are estimated. This is a necessary estimate for every matched transport;
it does not depend on a particular cutoff construction.

Only derivatives in the open interval are bounded. Continuity at the two
ends suffices, so the estimate applies to the open `unitStrip` used by
`CurrentJetDataOn`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The endpoint jump is controlled by the derivative bound on the open
transition interval. No derivative bound at either endpoint is needed. -/
theorem n04PositiveGeometry_endpointJump_le
    {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hbound : ∀ x ∈ Ioo a b, |deriv f x| ≤ M) :
    |f b - f a| ≤ M * (b - a) := by
  obtain ⟨x, hx, he⟩ := exists_deriv_eq_slope f hab hc hd
  have hh := hbound x hx
  rw [he, abs_div, abs_of_pos (sub_pos.mpr hab)] at hh
  exact (div_le_iff₀ (sub_pos.mpr hab)).mp hh

/-- In any supplied radial coordinate, a right endpoint displacement
forces a cost inversely proportional to the unfrozen interval width. -/
theorem n04PositiveGeometry_transport_rightBufferCost
    {τ σ : PolarPoint → PolarPoint} {l r c d J a b M θ : ℝ}
    (hgeometry : WholeComponentTransportGeometry τ σ l r c d J)
    (hcd : c ≤ d) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (ha : χ a = d) (hb : χ b = r) (hab : a < b)
    (hbound : ∀ y ∈ Ioo a b,
      |deriv (fun t => (τ (χ t, θ)).2 - θ) y| ≤ M) :
    |(τ (r, θ)).2 - θ| ≤ M * (b - a) := by
  let f : ℝ → ℝ := fun y => (τ (χ y, θ)).2 - θ
  have hf : ContDiff ℝ ∞ f :=
    (hgeometry.smooth.snd.comp (hχ.prodMk contDiff_const)).sub contDiff_const
  have hmid : τ (d, θ) = (d, θ) :=
    (hgeometry.middle_germ d ⟨hcd, le_rfl⟩ θ).eq_of_nhds
  have hfa : f a = 0 := by
    simp only [f, ha, hmid, sub_self]
  have hfb : f b = (τ (r, θ)).2 - θ := by
    simp only [f, hb]
  have h := n04PositiveGeometry_endpointJump_le hab hf.continuous.continuousOn
    (hf.differentiable (by simp)).differentiableOn hbound
  simpa only [hfa, hfb, sub_zero] using h

/-- A nonzero jump cannot be accommodated by a proposed derivative cost
when the supplied frozen middle leaves a smaller transition interval. -/
theorem n04PositiveGeometry_not_rightBufferBound
    {τ σ : PolarPoint → PolarPoint} {l r c d J a b M θ : ℝ}
    (hgeometry : WholeComponentTransportGeometry τ σ l r c d J)
    (hcd : c ≤ d) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (ha : χ a = d) (hb : χ b = r) (hab : a < b)
    (hsmall : M * (b - a) < |(τ (r, θ)).2 - θ|) :
    ¬ ∀ y ∈ Ioo a b,
      |deriv (fun t => (τ (χ t, θ)).2 - θ) y| ≤ M := by
  intro hbound
  exact (not_lt_of_ge (n04PositiveGeometry_transport_rightBufferCost
    hgeometry hcd χ hχ ha hb hab hbound)) hsmall

/-- Small state amplitudes do not remove the width obstruction: the
same positive amplitude occurs in the boundary jump and its tame bound. -/
theorem n04PositiveGeometry_cancel_amplitude
    {a K δ : ℝ} (ha : 0 < a) (h : a ≤ (K * a) * δ) : 1 ≤ K * δ := by
  have h' : a * 1 ≤ a * (K * δ) := by nlinarith only [h]
  exact le_of_mul_le_mul_left h' ha

end ContinuousFlexibility.Analysis
