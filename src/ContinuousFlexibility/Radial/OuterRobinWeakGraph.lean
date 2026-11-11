import ContinuousFlexibility.Radial.OuterSolutionOneSided
import ContinuousFlexibility.Radial.OuterRobinUniqueness

/-!
# The one-ended maximal weak Robin graph

The graph uses an actual C¹ value representative and its continuous
one-sided conormal flux.  Its first-order weak equation is exactly
`(w u')' = J w'/x u - ρ f`.  The value is in the given L² space, which
is the natural endpoint condition.  No inverse is part of this definition.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Analysis

def OuterRobinWeakGraph (μ : Measure ℝ) (a b J lam : ℝ)
    (w ρ : ℝ → ℝ) (v : ℝ × ℝ) (u f : Lp ℝ 2 μ) : Prop :=
  ∃ value flux : ℝ → ℝ,
    (u : ℝ → ℝ) =ᵐ[μ] value ∧
      ContDiffOn ℝ 1 value (Ico a b) ∧ ContinuousOn flux (Ico a b) ∧
      (∀ x ∈ Ico a b, flux x = w x * derivWithin value (Ico a b) x) ∧
      HasIntervalWeakDerivative a b flux
        (fun x => J * deriv w x / x * value x - ρ x * f x) ∧
      outerStatePair v (value a, flux a / lam) = 0

theorem outer_intervalWeakDerivative_sub {a b : ℝ} {q₀ q₁ g₀ g₁ : ℝ → ℝ}
    (hq₀ : LocallyIntegrableOn q₀ (Ioo a b))
    (hq₁ : LocallyIntegrableOn q₁ (Ioo a b))
    (hg₀ : LocallyIntegrableOn g₀ (Ioo a b))
    (hg₁ : LocallyIntegrableOn g₁ (Ioo a b))
    (h₀ : HasIntervalWeakDerivative a b q₀ g₀)
    (h₁ : HasIntervalWeakDerivative a b q₁ g₁) :
    HasIntervalWeakDerivative a b (fun x => q₀ x - q₁ x) (fun x => g₀ x - g₁ x) := by
  intro ψ hψ hc hs
  have hdψ := (contDiff_infty_iff_deriv.mp hψ).2.continuous
  have hds := tsupport_deriv_subset.trans hs
  have hq₀i := interval_integrable_mul_test hq₀ hdψ hc.deriv hds
  have hq₁i := interval_integrable_mul_test hq₁ hdψ hc.deriv hds
  have hg₀i := interval_integrable_mul_test hg₀ hψ.continuous hc hs
  have hg₁i := interval_integrable_mul_test hg₁ hψ.continuous hc hs
  change (∫ x, (q₀ x - q₁ x) * deriv ψ x) =
    -(∫ x, (g₀ x - g₁ x) * ψ x)
  simp_rw [sub_mul]
  rw [integral_sub hq₀i hq₁i, integral_sub hg₀i hg₁i,
    h₀ ψ hψ hc hs, h₁ ψ hψ hc hs]
  ring

/-- Two weak graph solutions with the same source differ by a genuine
homogeneous state.  Their one-sided Robin states also subtract exactly. -/
theorem OuterRobinWeakGraph.homogeneous_difference
    {μ : Measure ℝ} {a b J lam : ℝ} {w ρ : ℝ → ℝ} {v : ℝ × ℝ}
    {U₀ U₁ f : Lp ℝ 2 μ} (hab : a < b) (hlam : lam ≠ 0)
    (hw : ∀ x ∈ Ico a b, w x ≠ 0)
    (hκ : ContinuousOn (fun x => J * deriv w x / x) (Ioo a b))
    (hf : LocallyIntegrableOn (fun x => ρ x * f x) (Ioo a b))
    (h₀ : OuterRobinWeakGraph μ a b J lam w ρ v U₀ f)
    (h₁ : OuterRobinWeakGraph μ a b J lam w ρ v U₁ f) :
    ∃ u z : ℝ → ℝ,
      ((U₀ - U₁ : Lp ℝ 2 μ) : ℝ → ℝ) =ᵐ[μ] u ∧
      ContinuousOn u (Ico a b) ∧ ContinuousOn z (Ico a b) ∧
      OuterFirstOrderSystem (fun x => lam / w x)
        (fun x => J * deriv w x / (lam * x)) u z (Ioo a b) ∧
      outerStatePair v (u a, z a) = 0 := by
  obtain ⟨u₀, q₀, hae₀, hu₀, hq₀, hflux₀, heq₀, hr₀⟩ := h₀
  obtain ⟨u₁, q₁, hae₁, hu₁, hq₁, hflux₁, heq₁, hr₁⟩ := h₁
  let u : ℝ → ℝ := fun x => u₀ x - u₁ x
  let z : ℝ → ℝ := fun x => (q₀ x - q₁ x) / lam
  have huc : ContinuousOn u (Ico a b) := hu₀.continuousOn.sub hu₁.continuousOn
  have hzc : ContinuousOn z (Ico a b) := (hq₀.sub hq₁).div_const lam
  have hg₀ := ((hκ.mul (hu₀.continuousOn.mono Ioo_subset_Ico_self)).locallyIntegrableOn
    measurableSet_Ioo).sub hf
  have hg₁ := ((hκ.mul (hu₁.continuousOn.mono Ioo_subset_Ico_self)).locallyIntegrableOn
    measurableSet_Ioo).sub hf
  have hweak := outer_intervalWeakDerivative_sub
    ((hq₀.mono Ioo_subset_Ico_self).locallyIntegrableOn measurableSet_Ioo)
    ((hq₁.mono Ioo_subset_Ico_self).locallyIntegrableOn measurableSet_Ioo)
    hg₀ hg₁ heq₀ heq₁
  change HasIntervalWeakDerivative a b (fun x => q₀ x - q₁ x)
    (fun x => (J * deriv w x / x * u₀ x - ρ x * f x) -
      (J * deriv w x / x * u₁ x - ρ x * f x)) at hweak
  have hsource : (fun x =>
      (J * deriv w x / x * u₀ x - ρ x * f x) -
        (J * deriv w x / x * u₁ x - ρ x * f x)) =
      (fun x => J * deriv w x / x * u x) := by
    funext x
    dsimp only [u]
    ring
  rw [hsource] at hweak
  have hdq := hasDerivAt_of_continuous_interval_weakDerivative hab
    ((hq₀.sub hq₁).mono Ioo_subset_Ico_self)
    (hκ.mul (huc.mono Ioo_subset_Ico_self)) hweak
  refine ⟨u, z, ?_, huc, hzc, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub U₀ U₁, hae₀, hae₁] with x hx h₀x h₁x
    simpa only [Pi.sub_apply, h₀x, h₁x] using hx
  · intro x hx
    have hxi := Ioo_subset_Ico_self hx
    have hn : Ico a b ∈ 𝓝 x :=
      mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Ico_self
    have hd₀ : HasDerivAt u₀ (q₀ x / w x) x := by
      apply ((hu₀.differentiableOn (by norm_num) x hxi).hasDerivWithinAt.hasDerivAt hn).congr_deriv
      rw [hflux₀ x hxi]
      field_simp [hw x hxi]
    have hd₁ : HasDerivAt u₁ (q₁ x / w x) x := by
      apply ((hu₁.differentiableOn (by norm_num) x hxi).hasDerivWithinAt.hasDerivAt hn).congr_deriv
      rw [hflux₁ x hxi]
      field_simp [hw x hxi]
    constructor
    · apply (hd₀.sub hd₁).congr_deriv
      dsimp only [z]
      field_simp [hlam, hw x hxi] <;> ring
    · apply ((hdq x hx).div_const lam).congr_deriv
      simp only [Pi.mul_apply, div_eq_mul_inv, mul_inv_rev]
      ring
  · change v.1 * (u₀ a - u₁ a) + v.2 * ((q₀ a - q₁ a) / lam) = 0
    change v.1 * u₀ a + v.2 * (q₀ a / lam) = 0 at hr₀
    change v.1 * u₁ a + v.2 * (q₁ a / lam) = 0 at hr₁
    linear_combination hr₀ - hr₁

end ContinuousFlexibility.Radial
