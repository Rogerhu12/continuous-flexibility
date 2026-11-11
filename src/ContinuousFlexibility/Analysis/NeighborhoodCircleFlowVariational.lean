import ContinuousFlexibility.Analysis.NeighborhoodCircleFlowBasic

/-!
# Actual angular derivative with continuous time dependence

The exact finite-difference formula gives the variational exponential.
The argument only differentiates in the angle, including at the endpoints
of the compact time interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

theorem continuousAngleFlow_hasDerivAt_angle_of_continuous {G dG Θ : PolarPoint → ℝ} {a b : ℝ}
    (hdG : Continuous dG)
    (hderiv : ∀ t x, HasDerivAt (fun y => G (t, y)) (dG (t, x)) x) (hΘ : ContinuousOn Θ (Icc a b ×ˢ (univ : Set ℝ)))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => Θ (t, η))
      (Real.exp (∫ r in a..t, dG (r, Θ (r, θ)))) θ := by
  let clamp : ℝ → ℝ := fun r => max a (min r b)
  have hclamp : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  have hclamp_mem (r : ℝ) : clamp r ∈ Icc a b :=
    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_right _ _)⟩
  have hclamp_eq (r : ℝ) (hr : r ∈ Icc a b) : clamp r = r := by
    dsimp only [clamp]
    rw [min_eq_left hr.2, max_eq_right hr.1]
  have hclamped : Continuous (fun p : PolarPoint => Θ (clamp p.1, p.2)) :=
    hΘ.comp_continuous ((hclamp.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hclamp_mem p.1, mem_univ p.2⟩)
  let K : ℝ × ℝ → ℝ := fun p =>
    continuousAngleSpeedSecant dG (p.2, (Θ (clamp p.2, θ), Θ (clamp p.2, p.1)))
  have hK : Continuous K :=
    (continuous_continuousAngleSpeedSecant hdG).comp
      (continuous_snd.prodMk
        ((hclamped.comp (continuous_snd.prodMk continuous_const)).prodMk
          (hclamped.comp (continuous_snd.prodMk continuous_fst))))
  have hKeq (η r : ℝ) (hr : r ∈ Icc a b) :
      K (η, r) = continuousAngleSpeedSecant dG (r, (Θ (r, θ), Θ (r, η))) := by
    dsimp only [K]
    rw [hclamp_eq r hr]
  have hIK (η : ℝ) : (∫ r in a..t, K (η, r)) =
      ∫ r in a..t, continuousAngleSpeedSecant dG (r, (Θ (r, θ), Θ (r, η))) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
    exact hKeq η r ⟨hr'.1, hr'.2.trans ht.2⟩
  have htime (η : ℝ) : ContinuousOn (fun r => Θ (r, η)) (Icc a t) :=
    hΘ.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨⟨hr.1, hr.2.trans ht.2⟩, mem_univ η⟩)
  have hdiff (η : ℝ) : Θ (t, η) - Θ (t, θ) =
      (η - θ) * Real.exp (∫ r in a..t, K (η, r)) := by
    rw [hIK η]
    simpa only [hinit] using continuousAngleFlow_difference_eq_mul_exp ht.1 hdG hderiv htime
      (fun r hr => hflow r ⟨hr.1, hr.2.trans_le ht.2⟩) η θ
  have hdiag : (∫ r in a..t, K (θ, r)) =
      ∫ r in a..t, dG (r, Θ (r, θ)) := by
    rw [hIK θ]
    simp only [continuousAngleSpeedSecant_diagonal]
  have hcont : Continuous (fun η => Real.exp (∫ r in a..t, K (η, r))) :=
    Real.continuous_exp.comp (continuous_parametric_intervalIntegral hK a t)
  have hlim : Tendsto (fun η => Real.exp (∫ r in a..t, K (η, r))) (𝓝[≠] θ)
      (𝓝 (Real.exp (∫ r in a..t, dG (r, Θ (r, θ))))) := by
    rw [← hdiag]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope : slope (fun η => Θ (t, η)) θ =ᶠ[𝓝[≠] θ]
      (fun η => Real.exp (∫ r in a..t, K (η, r))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [slope_def_field, hdiff η]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hη)
  exact hasDerivAt_iff_tendsto_slope.mpr ((tendsto_congr' hslope).mpr hlim)

end ContinuousFlexibility.Analysis
