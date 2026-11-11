import ContinuousFlexibility.Radial.MorseRadiusODE
import ContinuousFlexibility.Radial.PositiveBufferRegularity

/-!
# Smooth continuation across positive-buffer cuts

A weak energy profile initially has only a continuous derivative from one
side of a cut. The smooth scalar initial-value problem and uniqueness on a
closed interval identify it with a smooth solution through both endpoints.
This provides the actual, two-sided derivatives appearing in the conormal
data of positive-buffer compression.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- A classical interior state with continuous endpoint values has a
globally smooth representative agreeing with the state and its first
derivative through both endpoints. -/
theorem positiveBuffer_finite_smooth_extension {V U D : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hV : ContDiff ℝ ∞ V)
    (hU : ContinuousOn U (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hUd : ∀ x ∈ Ioo a b, HasDerivAt U (D x) x)
    (hDd : ∀ x ∈ Ioo a b, HasDerivAt D (V x * U x) x) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ EqOn p U (Icc a b) ∧
      EqOn (deriv p) D (Icc a b) ∧
      ∀ x ∈ Ioo (a - 1) (b + 1), -deriv (deriv p) x + V x * p x = 0 := by
  let t₀ : ℝ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := ⟨by dsimp only [t₀]; linarith,
    by dsimp only [t₀]; linarith⟩
  obtain ⟨p, d, hp, hd, hp₀, hd₀, hpd⟩ :=
    exists_smoothSecondOrderSystem hV.neg (Ioo_subset_Icc_self ht₀) (U t₀) (D t₀)
  have hsub : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
    intro x hx
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hDd' : ∀ x ∈ Ioo a b, HasDerivAt D (-(fun x => -V x) x * U x) x := by
    simpa only [neg_neg] using hDd
  have heq := smoothScalarSystem_eqOn hV.continuous.neg ht₀ hU hD
    hp.continuous.continuousOn hd.continuous.continuousOn hUd hDd'
    (fun x hx => (hpd x (hsub (Ioo_subset_Icc_self hx))).1)
    (fun x hx => (hpd x (hsub (Ioo_subset_Icc_self hx))).2) hp₀.symm hd₀.symm
  refine ⟨p, hp, heq.1.symm, ?_, ?_⟩
  · intro x hx
    exact (hpd x (hsub hx)).1.deriv.trans (heq.2 hx).symm
  · intro x hx
    have he : deriv p =ᶠ[𝓝 x] d := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (hpd y hy).1.deriv
    have hsecond : deriv (deriv p) x = V x * p x := by
      simpa only [Pi.neg_apply, neg_neg] using he.deriv_eq.trans (hpd x hx).2.deriv
    rw [hsecond]
    ring

end ContinuousFlexibility.Radial
