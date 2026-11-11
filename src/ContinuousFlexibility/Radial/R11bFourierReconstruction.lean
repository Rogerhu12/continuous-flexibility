import ContinuousFlexibility.Radial.R11bEvenSeriesCoefficients
import ContinuousFlexibility.Radial.R11bPhysicalL2Convergence
import ContinuousFlexibility.Radial.R11bSymmetricLimit

/-!
# Strong physical reconstruction from the actual even Fourier coefficients

The mean and all positive even modes are included. Radial coefficient
representatives may be replaced almost everywhere, so smooth mode
representatives can be used in the original finite tensor sums.
-/

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Actual finite Fourier sums, with any a.e. equal radial coefficient
representatives, converge strongly to the original physical L² field. -/
theorem r11b_even_partialSums_tendsto_of_coefficients
    {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hup : ∀ r, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (hue : ∀ r, Function.Even (fun θ => u (r, θ)))
    (c : ℕ → ℝ → ℝ)
    (hcEq : ∀ n, c n =ᵐ[volume.restrict (radialCore D)] evenFourierCoefficient u n) :
    ∃ hP : ∀ N, MemLp (r11bEvenPartialSum c N) 2 (radialPhysicalMeasure D),
      Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum c N))
        atTop (𝓝 (hu.toLp u)) := by
  let μ : Measure ℝ := volume.restrict (radialCore D)
  have hun : MemLp u 2 (μ.prod angularMeanMeasure) :=
    r11b_memLp_radial_angularMean hu
  have hc : ∀ n, MemLp (c n) 2 μ := fun n =>
    MemLp.ae_eq (hcEq n).symm (evenFourierCoefficient_memLp hun n)
  have hcInt (n : ℕ) :
      (∫ r, c n r ^ 2 ∂μ) = ∫ r, evenFourierCoefficient u n r ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hcEq n] with r hr
    exact congrArg (fun t : ℝ => t ^ 2) hr
  have hsq : Summable (fun n => ∫ r, c n r ^ 2 ∂μ) :=
    (evenFourierCoefficient_energy_summable hun).congr (fun n => (hcInt n).symm)
  let V : Lp ℝ 2 (μ.prod angularMeanMeasure) :=
    ∑' n, r11bTensorL2 (hc n) (evenCosineBasis_memLp n)
  have hP (N : ℕ) : MemLp (r11bEvenPartialSum c N) 2 (μ.prod angularMeanMeasure) :=
    r11bEvenPartialSum_memLp c hc N
  have hlim : Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum c N))
      atTop (𝓝 V) :=
    r11bEvenPartialSum_tendsto c hc hsq
  obtain ⟨g, hg, hgv, hgp, hge⟩ :=
    r11b_symmetric_representative_of_L2_tendsto hP
      (r11bEvenPartialSum_periodic c) (r11bEvenPartialSum_even c) hlim
  have hcg (n : ℕ) : evenFourierCoefficient g n =ᵐ[μ] c n := by
    have hs : r11bModeCoefficientLp (evenCosineBasis_memLp n) V = (hc n).toLp (c n) :=
      r11bEvenSeries_coefficientLp c hc hsq n
    have hclass :
        (r11bModeCoefficientLp (evenCosineBasis_memLp n) V : ℝ → ℝ) =ᵐ[μ] c n := by
      rw [hs]
      exact (hc n).coeFn_toLp
    have hraw := r11b_modeCoefficient_congr_ae hgv (evenCosineBasis n)
    have hrepr := r11bModeCoefficientLp_coeFn (evenCosineBasis_memLp n) V
    rw [evenFourierCoefficient_eq_integral]
    exact hraw.trans (hrepr.symm.trans hclass)
  have hgphys : MemLp g 2 (radialPhysicalMeasure D) :=
    r11b_memLp_of_radial_angularMean (D := D) hg
  have hgu : g =ᵐ[radialPhysicalMeasure D] u := by
    apply r11b_physical_ae_eq_of_referenceModes hgphys hu hge hue hgp hup
    · filter_upwards [(hcg 0).trans (hcEq 0)] with r hr
      simpa only [evenFourierCoefficient_zero_physical] using hr
    · intro j hj hjEven
      obtain ⟨n, hn⟩ := hjEven
      have hjn : j = 2 * n := by omega
      have hn0 : n ≠ 0 := by omega
      have h := (hcg n).trans (hcEq n)
      rw [evenFourierCoefficient_eq_referenceMode g hn0,
        evenFourierCoefficient_eq_referenceMode u hn0] at h
      simpa only [hjn] using h
  have hgV : hg.toLp g = V := by
    apply Lp.ext
    exact hg.coeFn_toLp.trans hgv
  have hlimG : Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum c N))
      atTop (𝓝 (hg.toLp g)) := by
    rw [hgV]
    exact hlim
  have hphysical := r11b_tendsto_toLp_physical_of_radial_angularMean (D := D) hP hg hlimG
  have hguLp : (r11b_memLp_of_radial_angularMean (D := D) hg).toLp g = hu.toLp u :=
    MemLp.toLp_congr _ _ hgu
  rw [hguLp] at hphysical
  exact ⟨fun N => r11b_memLp_of_radial_angularMean (D := D) (hP N), hphysical⟩

theorem r11b_even_fourier_partialSums_tendsto
    {D : ReferenceData} {u : PolarPoint → ℝ}
    (hu : MemLp u 2 (radialPhysicalMeasure D))
    (hup : ∀ r, Function.Periodic (fun θ => u (r, θ)) Real.pi)
    (hue : ∀ r, Function.Even (fun θ => u (r, θ))) :
    ∃ hP : ∀ N, MemLp (r11bEvenPartialSum (evenFourierCoefficient u) N) 2
        (radialPhysicalMeasure D),
      Tendsto (fun N => (hP N).toLp (r11bEvenPartialSum (evenFourierCoefficient u) N))
        atTop (𝓝 (hu.toLp u)) :=
  r11b_even_partialSums_tendsto_of_coefficients hu hup hue
    (evenFourierCoefficient u) (fun _ => Filter.EventuallyEq.rfl)

end

end ContinuousFlexibility.Radial
