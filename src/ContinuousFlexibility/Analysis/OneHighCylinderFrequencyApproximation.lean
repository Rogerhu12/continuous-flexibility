import ContinuousFlexibility.Analysis.OneHighCylinderFourierCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Strong convergence of bounded-frequency cutoffs

Every fixed mixed frequency eventually belongs to the cutoff. Dominated
convergence gives actual L1 and L2 convergence, including the weighted L2
norm whenever that finite Sobolev membership is given.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal Topology

variable {P : ℝ}

theorem cylinderFrequencyCutoff_eventually_eq (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ∀ᶠ N : ℕ in atTop, cylinderFrequencyCutoff (P := P) N F ζ = F ζ := by
  obtain ⟨N, hN⟩ := exists_nat_ge
    (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact if_pos (hN.trans (Nat.cast_le.mpr hn))

theorem norm_cylinderFrequencyCutoff_sub_le (N : ℕ) (F : ℝ × ℤ → ℂ) (ζ : ℝ × ℤ) :
    ‖cylinderFrequencyCutoff (P := P) N F ζ - F ζ‖ ≤ ‖F ζ‖ := by
  by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
  · simp only [cylinderFrequencyCutoff, if_pos h, sub_self, norm_zero]
    exact norm_nonneg _
  · simp only [cylinderFrequencyCutoff, if_neg h, zero_sub, norm_neg, le_refl]

private theorem cylinder_l2_toReal_eq_sqrt_integral {F : ℝ × ℤ → ℂ}
    (hF : AEStronglyMeasurable F cylinderFrequencyMeasure) :
    (eLpNorm F 2 cylinderFrequencyMeasure).toReal =
      Real.sqrt (∫ ζ, ‖F ζ‖ ^ 2 ∂cylinderFrequencyMeasure) := by
  rw [toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top hF]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]

theorem cylinderFrequencyCutoff_tendsto_l2 {F : ℝ × ℤ → ℂ}
    (hF : MemLp F 2 cylinderFrequencyMeasure) :
    Tendsto (fun N : ℕ => (eLpNorm
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ)
        2 cylinderFrequencyMeasure).toReal) atTop (𝓝 0) := by
  have hm (N : ℕ) : MemLp
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ)
        2 cylinderFrequencyMeasure := (cylinderFrequencyCutoff_memLp hF N).sub hF
  have hi : Tendsto (fun N : ℕ => ∫ ζ,
      ‖cylinderFrequencyCutoff (P := P) N F ζ - F ζ‖ ^ 2
        ∂cylinderFrequencyMeasure) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := cylinderFrequencyMeasure)
      (F := fun N ζ => ‖cylinderFrequencyCutoff (P := P) N F ζ - F ζ‖ ^ 2)
      (f := fun _ => (0 : ℝ)) (fun ζ => ‖F ζ‖ ^ 2)
      (fun N => (hm N).aestronglyMeasurable.norm.pow 2)
      (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (fun N => Eventually.of_forall fun ζ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_cylinderFrequencyCutoff_sub_le N F ζ) 2)
      (Eventually.of_forall fun ζ => by
        apply tendsto_const_nhds.congr'
        filter_upwards [cylinderFrequencyCutoff_eventually_eq (P := P) F ζ] with N hN
        simp only [hN, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
    simpa only [integral_zero] using h
  have he (N : ℕ) : (eLpNorm
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ)
        2 cylinderFrequencyMeasure).toReal =
      Real.sqrt (∫ ζ, ‖cylinderFrequencyCutoff (P := P) N F ζ - F ζ‖ ^ 2
        ∂cylinderFrequencyMeasure) :=
    cylinder_l2_toReal_eq_sqrt_integral (hm N).aestronglyMeasurable
  simpa only [Function.comp_def, Real.sqrt_zero, ← he] using
    (Real.continuous_sqrt.tendsto 0).comp hi

theorem cylinderFrequencyCutoff_tendsto_l1 {F : ℝ × ℤ → ℂ}
    (hF : Integrable F cylinderFrequencyMeasure) :
    Tendsto (fun N : ℕ => frequencyL1Norm cylinderFrequencyMeasure
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ)) atTop (𝓝 0) := by
  have hm (N : ℕ) : Integrable
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ) cylinderFrequencyMeasure :=
    (integrable_cylinderFrequencyCutoff hF N).sub hF
  have hi := tendsto_integral_of_dominated_convergence
    (μ := cylinderFrequencyMeasure)
    (F := fun N ζ => ‖cylinderFrequencyCutoff (P := P) N F ζ - F ζ‖)
    (f := fun _ => (0 : ℝ)) (fun ζ => ‖F ζ‖)
    (fun N => (hm N).aestronglyMeasurable.norm) hF.norm
    (fun N => Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_cylinderFrequencyCutoff_sub_le N F ζ)
    (Eventually.of_forall fun ζ => by
      apply tendsto_const_nhds.congr'
      filter_upwards [cylinderFrequencyCutoff_eventually_eq (P := P) F ζ] with N hN
      simp only [hN, sub_self, norm_zero])
  have he (N : ℕ) : frequencyL1Norm cylinderFrequencyMeasure
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ) =
      ∫ ζ, ‖cylinderFrequencyCutoff (P := P) N F ζ - F ζ‖ ∂cylinderFrequencyMeasure := by
    exact lpNorm_one_eq_integral_norm (hm N).aestronglyMeasurable
  simpa only [integral_zero, ← he] using hi

theorem cylinderFrequencyCutoff_tendsto_sobolev {F : ℝ × ℤ → ℂ} {s : ℝ}
    (hF : MemLp (frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F)
        2 cylinderFrequencyMeasure) :
    Tendsto (fun N : ℕ => frequencySobolevNorm cylinderFrequencyMeasure
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ)) atTop (𝓝 0) := by
  have he (N : ℕ) : frequencyWeighted
      (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s
      (fun ζ => cylinderFrequencyCutoff (P := P) N F ζ - F ζ) =
      fun ζ => cylinderFrequencyCutoff (P := P) N
        (frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F) ζ -
          frequencyWeighted (cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P)) s F ζ := by
    funext ζ
    by_cases h : cylinderFrequencyWeight (2 * Real.pi) (2 * Real.pi / P) ζ ≤ (N : ℝ)
    · simp only [frequencyWeighted_apply, cylinderFrequencyCutoff, if_pos h, sub_self, smul_zero]
    · simp only [frequencyWeighted_apply, cylinderFrequencyCutoff, if_neg h, zero_sub, smul_neg]
  simpa only [frequencySobolevNorm, he] using
    (cylinderFrequencyCutoff_tendsto_l2 (P := P) hF)

end ContinuousFlexibility.Analysis
