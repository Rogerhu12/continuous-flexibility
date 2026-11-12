import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients

/-! # Canonical L² representatives of actual bounded open coefficients

This finite-measure construction is independent of physical test pullbacks.
It retains the same actual value function used by the coefficient algebra.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

namespace N07aCanonicalOpenCoefficient

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem memLp (χ : N07aCanonicalOpenCoefficient S K m) :
    MemLp χ.value 2 (canonicalMeasure S K m) := by
  let := n07a_canonicalMeasure_finite S K m
  apply MemLp.of_bound (n07a_canonicalOpen_aestronglyMeasurable χ.smooth.continuousOn) χ.bound
  simpa only [Real.norm_eq_abs] using χ.bound_ae

def toLp (χ : N07aCanonicalOpenCoefficient S K m) : CanonicalL2 S K m :=
  χ.memLp.toLp χ.value

theorem toLp_ae (χ : N07aCanonicalOpenCoefficient S K m) :
    (χ.toLp : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] χ.value :=
  χ.memLp.coeFn_toLp

end N07aCanonicalOpenCoefficient

end ContinuousFlexibility.Analysis
