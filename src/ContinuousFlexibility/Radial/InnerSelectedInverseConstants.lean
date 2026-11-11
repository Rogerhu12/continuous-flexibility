import ContinuousFlexibility.Radial.InnerSelectedDirichletCosts
import ContinuousFlexibility.Radial.InnerSelectedInterfaceEstimates
import ContinuousFlexibility.Radial.InnerCoefficientCosts

/-!
# Constants for both estimates of the same inner inverse

The local loss is the fixed exponent thirty-seven. The constant in
the localized estimate may depend on the chosen first index, while
the coarse exponent absorbs all multiplicative constants uniformly
over the later transition index and frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

/-- Every positive even frequency absorbs the correction denominator
without introducing a frequency-dependent constant. -/
theorem inner_selected_even_correction_le (C : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    2 * C ^ 2 / ((2 : ℝ) * q) ^ 2 ≤ 2 * C ^ 2 := by
  have hj : 1 ≤ (2 : ℝ) * q := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hjpos : 0 < (2 : ℝ) * q := zero_lt_one.trans_le hj
  have hj2 : 1 ≤ ((2 : ℝ) * q) ^ 2 := by
    nlinarith only [hj, sq_nonneg ((2 : ℝ) * q - 1)]
  apply (div_le_iff₀ (sq_pos_of_pos hjpos)).mpr
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hj2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C))

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

/-- Only the fixed geometry, first index, and original R09 constants
enter the localized inverse constant. -/
def inverseLocalizedConstant (CC CM : ℝ) : ℝ :=
  P.dirichletConstant CC CM * radialE S.chain.index ^ (37 : ℝ) +
    2 * P.poissonConstant ^ 2

def inverseCoarseExponent (CC CM : ℝ) : ℝ :=
  37 + (P.dirichletConstant CC CM + 2 * P.poissonConstant ^ 2 + 1)

/-- One constant is used in the Poisson bound, the localized inverse
bound, and the exponent of the coarse inverse bound. -/
def inverseEstimateConstant (CC CM : ℝ) : ℝ :=
  max P.poissonConstant (max (P.inverseLocalizedConstant CC CM) (P.inverseCoarseExponent CC CM))

theorem inverseEstimateConstant_pos (CC CM : ℝ) :
    0 < P.inverseEstimateConstant CC CM :=
  P.poissonConstant_pos.trans_le (le_max_left _ _)

theorem poissonConstant_le_inverseEstimateConstant (CC CM : ℝ) :
    P.poissonConstant ≤ P.inverseEstimateConstant CC CM := le_max_left _ _

theorem inverseLocalizedConstant_le_inverseEstimateConstant (CC CM : ℝ) :
    P.inverseLocalizedConstant CC CM ≤ P.inverseEstimateConstant CC CM :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem inverseCoarseExponent_le_inverseEstimateConstant (CC CM : ℝ) :
    P.inverseCoarseExponent CC CM ≤ P.inverseEstimateConstant CC CM :=
  (le_max_right _ _).trans (le_max_right _ _)

include P

/-- The coefficient at every transition index has logarithm at least
one, so fixed costs can be absorbed into its exponent. -/
theorem band_coefficient_log_ge_one (K : ℕ) :
    1 ≤ radialQ (S.chain.index + K) := by
  have hn : (1 : ℝ) ≤ (S.chain.index + K : ℕ) := by
    exact_mod_cast (show 1 ≤ S.chain.index + K by have := P.index_ge; omega)
  exact (by nlinarith only [hn] : (1 : ℝ) ≤ ((S.chain.index + K : ℕ) : ℝ) ^ 2).trans
    (radial_nat_sq_le_Q (S.chain.index + K))

theorem coarse_cost_and_correction (CC CM : ℝ) (K q : ℕ) (hq : 1 ≤ q) :
    P.dirichletConstant CC CM * radialE (S.chain.index + K) ^ (37 : ℝ) +
      2 * P.poissonConstant ^ 2 / ((2 : ℝ) * q) ^ 2 ≤
        radialE (S.chain.index + K) ^ P.inverseCoarseExponent CC CM := by
  apply (add_le_add le_rfl (inner_selected_even_correction_le P.poissonConstant hq)).trans
  exact inner_coefficient_absorb_cost_and_correction
    (P.dirichletConstant_pos CC CM).le (by positivity) (by norm_num)
    (P.band_coefficient_log_ge_one K)

theorem coarse_power_le_inverseEstimateConstant (CC CM : ℝ) (K : ℕ) :
    radialE (S.chain.index + K) ^ P.inverseCoarseExponent CC CM ≤
      radialE (S.chain.index + K) ^ P.inverseEstimateConstant CC CM := by
  apply rpow_le_rpow_of_exponent_le
  · exact one_le_exp_iff.mpr (radialQ_nonneg (S.chain.index + K))
  · exact P.inverseCoarseExponent_le_inverseEstimateConstant CC CM

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
