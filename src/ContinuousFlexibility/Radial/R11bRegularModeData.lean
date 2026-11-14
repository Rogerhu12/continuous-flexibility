module

public import ContinuousFlexibility.Radial.R11bEvenModeRegularity
public import ContinuousFlexibility.Radial.R11bRemainderModes

/-!
# A common countable family of actual radial mode representatives

The chosen C1 representatives point toward the original angular
coefficients. Subtracting the left radial correction changes only the
mean channel, and this identity holds on the radial full-measure set.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_evenFourierCoefficient_outputRemainder_ae
    {D : ReferenceData} {U : RadialUnknown}
    (hU : MemLp U.1 2 (radialPhysicalMeasure D)) (a : ℝ) (n : ℕ) :
    evenFourierCoefficient (outputRemainder D a U) n
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => evenFourierCoefficient U.1 n r -
          (if n = 0 then a else 0) * D.chiLeft r) := by
  by_cases hn : n = 0
  · subst n
    filter_upwards [r11b_radialAngularMean_outputRemainder_ae hU a] with r hr
    simpa only [evenFourierCoefficient_zero_physical, if_pos rfl, ite_true] using hr
  · have hj : 0 < 2 * n := by omega
    filter_upwards [r11b_referenceMode_outputRemainder_ae hU a (2 * n) hj] with r hr
    simpa only [evenFourierCoefficient_eq_referenceMode (outputRemainder D a U) hn,
      evenFourierCoefficient_eq_referenceMode U.1 hn, if_neg hn, zero_mul, sub_zero] using hr

/-- All even coefficients admit one simultaneously chosen family of C1
representatives and primitive-flux constants at a common interior origin. -/
theorem r11b_exists_evenModeData {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (r₀ : ℝ) (hr₀ : r₀ ∈ radialCore D) :
    ∃ c : ℕ → ℝ → ℝ, ∃ q : ℕ → ℝ,
      (∀ n, c n =ᵐ[volume.restrict (radialCore D)] evenFourierCoefficient U.1 n) ∧
      (∀ n, ContDiffOn ℝ 1 (c n) (radialCore D)) ∧
      (∀ n, MemLp (c n) 2 (volume.restrict (radialCore D))) ∧
      (∀ n r, r ∈ radialCore D → D.w r * deriv (c n) r =
        intervalLocalPrimitive
          (fun t => r11bEvenModeForcing D U F n t +
            c n t * (((2 * n : ℕ) : ℝ) ^ 2 * deriv D.w t / t)) r₀ r + q n) ∧
      (∀ a n, (fun r => c n r - (if n = 0 then a else 0) * D.chiLeft r)
        =ᵐ[volume.restrict (radialCore D)]
          evenFourierCoefficient (outputRemainder D a U) n) := by
  classical
  choose c q hcoeff hc hflux using
    fun n => r11b_evenCoefficient_contDiffOn_one_representative
      hD hborder hγ hUF n r₀ hr₀
  have hU : MemLp U.1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ hUF.1
  refine ⟨c, q, fun n => (hcoeff n).symm, hc, ?_, hflux, ?_⟩
  · intro n
    exact MemLp.ae_eq (hcoeff n)
      (evenFourierCoefficient_memLp (r11b_memLp_radial_angularMean hU) n)
  · intro a n
    filter_upwards [hcoeff n, r11b_evenFourierCoefficient_outputRemainder_ae hU a n]
      with r hcr hrr
    change c n r - (if n = 0 then a else 0) * D.chiLeft r =
      evenFourierCoefficient (outputRemainder D a U) n r
    exact (congrArg (fun t : ℝ => t - (if n = 0 then a else 0) * D.chiLeft r)
      hcr.symm).trans hrr.symm

end

end ContinuousFlexibility.Radial
