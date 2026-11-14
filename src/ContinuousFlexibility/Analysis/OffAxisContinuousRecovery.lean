import ContinuousFlexibility.Analysis.ClosureOperatorFaithfulness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Continuous recovery from the complement of the reflection axes

At a doubled-sine zero, a short positive angular segment avoids every
other zero. Actual continuity therefore extends an identity known off
the axes to every point of an open physical domain. This uses no value
or derivative convention for a prospective stored coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

theorem scalar_eq_of_offAxis_on_open
    {U : Set PolarPoint} (hU : IsOpen U) {f g : PolarPoint → ℝ}
    {p : PolarPoint} (hp : p ∈ U)
    (hf : ContinuousAt f p) (hg : ContinuousAt g p)
    (he : ∀ q ∈ U, Real.sin (2 * q.2) ≠ 0 → f q = g q) : f p = g p := by
  by_cases haxis : Real.sin (2 * p.2) = 0
  · let γ : ℝ → PolarPoint := fun t => (p.1, p.2 + t)
    have hγ : Continuous γ :=
      continuous_const.prodMk (continuous_const.add continuous_id)
    have hγ0 : ContinuousAt γ 0 := hγ.continuousAt
    have hlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 p) := by
      simpa only [γ, add_zero, Prod.eta] using hγ0.mono_left nhdsWithin_le_nhds
    have hcos : Real.cos (2 * p.2) ≠ 0 := by
      have hsq := Real.sin_sq_add_cos_sq (2 * p.2)
      rw [haxis, zero_pow two_ne_zero, zero_add] at hsq
      intro hz
      rw [hz] at hsq
      norm_num at hsq
    have hevent : (fun t => f (γ t)) =ᶠ[𝓝[>] (0 : ℝ)] (fun t => g (γ t)) := by
      filter_upwards [hlim.eventually (hU.mem_nhds hp),
        Ioo_mem_nhdsGT (half_pos Real.pi_pos)] with t ht hsmall
      apply he (γ t) ht
      change Real.sin (2 * (p.2 + t)) ≠ 0
      rw [show 2 * (p.2 + t) = 2 * p.2 + 2 * t by ring,
        Real.sin_add, haxis, zero_mul, zero_add]
      exact mul_ne_zero hcos (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hsmall.1]) (by linarith [hsmall.2])).ne'
    exact tendsto_nhds_unique_of_eventuallyEq
      (hf.tendsto.comp hlim) (hg.tendsto.comp hlim) hevent
  · exact he p hp haxis

end ContinuousFlexibility.Analysis
