import ContinuousFlexibility.Analysis.N07aAngularBands
import ContinuousFlexibility.Analysis.N07aAngularWeights

/-!
# Arbitrarily high true weak jets in a fixed angular band

A single band retains infinitely many radial Fourier indices, but its
angular derivative multiplier is bounded. Real Fourier inversion thus
constructs every weak angular derivative of that band on the original
canonical piece. Its norm is computed exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ComplexConjugate

set_option backward.isDefEq.respectTransparency false

theorem n07aAngularSymbol_norm (j : SpacesTorusFrequency) (k : ℕ) :
    ‖(2 * Complex.I * (j 1 : ℂ)) ^ k‖ =
      (2 * (n07aAngularFrequency j : ℝ)) ^ k := by
  simp only [norm_pow, norm_mul, Complex.norm_two, Complex.norm_I,
    Complex.norm_intCast, mul_one, n07aAngularFrequency]
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem n07aAngularSymbol_neg (j : SpacesTorusFrequency) (k : ℕ) :
    (2 * Complex.I * ((-j) 1 : ℂ)) ^ k = conj ((2 * Complex.I * (j 1 : ℂ)) ^ k) := by
  rw [map_pow]
  congr 1
  simp only [Pi.neg_apply, Int.cast_neg, map_mul, map_ofNat, Complex.conj_I, map_intCast]
  ring

private def n07aAngularBandDerivativeCoefficientsFun (n k : ℕ)
    (u : SpacesTorusCoefficients) (j : SpacesTorusFrequency) : ℂ :=
  (2 * Complex.I * (j 1 : ℂ)) ^ k * lpSpectralBand n07aAngularFrequency n u j

private theorem n07aAngularBandDerivativeCoefficientsFun_norm (n k : ℕ)
    (u : SpacesTorusCoefficients) (j : SpacesTorusFrequency) :
    ‖n07aAngularBandDerivativeCoefficientsFun n k u j‖ =
      (2 * (n : ℝ)) ^ k * ‖lpSpectralBand n07aAngularFrequency n u j‖ := by
  rw [n07aAngularBandDerivativeCoefficientsFun, norm_mul, n07aAngularSymbol_norm]
  by_cases hj : n07aAngularFrequency j = n
  · rw [hj]
  · rw [lpSpectralBand_apply, if_neg hj, norm_zero, mul_zero, mul_zero]

def n07aAngularBandDerivativeCoefficients (n k : ℕ)
    (u : SpacesTorusCoefficients) : SpacesTorusCoefficients :=
  ⟨n07aAngularBandDerivativeCoefficientsFun n k u,
    (lp.memℓp ((2 * (n : ℝ)) ^ k • lpSpectralBand n07aAngularFrequency n u)).mono' (fun j => by
      rw [n07aAngularBandDerivativeCoefficientsFun_norm, lp.coeFn_smul,
        Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)])⟩

@[simp] theorem n07aAngularBandDerivativeCoefficients_apply (n k : ℕ)
    (u : SpacesTorusCoefficients) (j : SpacesTorusFrequency) :
    n07aAngularBandDerivativeCoefficients n k u j =
      (2 * Complex.I * (j 1 : ℂ)) ^ k * lpSpectralBand n07aAngularFrequency n u j := rfl

theorem n07aAngularBandDerivativeCoefficients_norm (n k : ℕ)
    (u : SpacesTorusCoefficients) :
    ‖n07aAngularBandDerivativeCoefficients n k u‖ =
      (2 * (n : ℝ)) ^ k * ‖lpSpectralBand n07aAngularFrequency n u‖ := by
  have he (j : SpacesTorusFrequency) :
      ‖n07aAngularBandDerivativeCoefficients n k u j‖ =
        ‖((2 * (n : ℝ)) ^ k • lpSpectralBand n07aAngularFrequency n u) j‖ := by
    rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact n07aAngularBandDerivativeCoefficientsFun_norm n k u j
  have hnorm : ‖n07aAngularBandDerivativeCoefficients n k u‖ =
      ‖(2 * (n : ℝ)) ^ k • lpSpectralBand n07aAngularFrequency n u‖ :=
    le_antisymm (lp.norm_mono (by norm_num) (fun j => (he j).le))
      (lp.norm_mono (by norm_num) (fun j => (he j).ge))
  rw [hnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem n07aAngularBandDerivativeCoefficients_neg (n k : ℕ)
    (u : SpacesTorusCoefficients) (hu : ∀ j, u (-j) = conj (u j)) (j : SpacesTorusFrequency) :
    n07aAngularBandDerivativeCoefficients n k u (-j) =
      conj (n07aAngularBandDerivativeCoefficients n k u j) := by
  simp only [n07aAngularBandDerivativeCoefficients_apply, n07aAngularSymbol_neg,
    lpSpectralBand_apply, n07aAngularFrequency_neg, hu, map_mul]
  split_ifs <;> simp only [map_zero]

variable {S : PhysicalSpacesData} {K : CanonicalData S}

/-- The actual `k`th weak angular derivative of the `n`th band. -/
def n07aAngularBandDerivative (m : ℕ) (hm : K.left m < K.right m) (n k : ℕ)
    (u : CanonicalL2 S K m) : CanonicalL2 S K m :=
  n07aAngularFourierInverse m hm
    (n07aAngularBandDerivativeCoefficients n k (n07aAngularFourier m hm u))

theorem n07aAngularBandDerivative_fourier (m : ℕ) (hm : K.left m < K.right m)
    (n k : ℕ) (u : CanonicalL2 S K m) :
    n07aAngularFourier m hm (n07aAngularBandDerivative m hm n k u) =
      n07aAngularBandDerivativeCoefficients n k (n07aAngularFourier m hm u) := by
  apply n07aAngularFourier_inverse
  exact n07aAngularBandDerivativeCoefficients_neg n k _ (n07aAngularFourier_neg m hm u)

theorem n07aAngularBandDerivative_coefficient (m : ℕ) (hm : K.left m < K.right m)
    (n k : ℕ) (u : CanonicalL2 S K m) (j : SpacesTorusFrequency) :
    n07aAngularFourier m hm (n07aAngularBandDerivative m hm n k u) j =
      (2 * Complex.I * (j 1 : ℂ)) ^ k * n07aAngularFourier m hm (n07aAngularBand m hm n u) j := by
  rw [n07aAngularBandDerivative_fourier, n07aAngularBandDerivativeCoefficients_apply,
    n07aAngularBand_fourier]

theorem n07aAngularBandDerivative_norm (m : ℕ) (hm : K.left m < K.right m)
    (n k : ℕ) (u : CanonicalL2 S K m) :
    ‖n07aAngularBandDerivative m hm n k u‖ = (2 * (n : ℝ)) ^ k * ‖n07aAngularBand m hm n u‖ := by
  rw [← (n07aAngularFourier m hm).norm_map (n07aAngularBandDerivative m hm n k u),
    n07aAngularBandDerivative_fourier, n07aAngularBandDerivativeCoefficients_norm,
    ← n07aAngularBand_fourier, LinearIsometry.norm_map]

theorem n07aAngularBandDerivative_zero (m : ℕ) (hm : K.left m < K.right m)
    (n : ℕ) (u : CanonicalL2 S K m) :
    n07aAngularBandDerivative m hm n 0 u = n07aAngularBand m hm n u := by
  apply (n07aAngularFourier m hm).injective
  apply lp.ext
  funext j
  rw [n07aAngularBandDerivative_coefficient, pow_zero, one_mul]

theorem n07aAngularBandDerivative_weak (m : ℕ) (hm : K.left m < K.right m)
    (n k : ℕ) (u : CanonicalL2 S K m) :
    WeakCanonicalAngularDerivative S K m
      (n07aAngularBand m hm n u) (n07aAngularBandDerivative m hm n k u) k :=
  n07aAngularWeak_of_fourier m hm (n07aAngularBandDerivative_coefficient m hm n k u)

theorem n07aAngularBandDerivative_band (m : ℕ) (hm : K.left m < K.right m)
    (n k : ℕ) (u : CanonicalL2 S K m) :
    n07aAngularBand m hm n (n07aAngularBandDerivative m hm n k u) =
      n07aAngularBandDerivative m hm n k u := by
  apply (n07aAngularFourier m hm).injective
  apply lp.ext
  funext j
  rw [n07aAngularBand_coefficient, n07aAngularBandDerivative_coefficient,
    n07aAngularBand_coefficient]
  split_ifs <;> simp only [mul_zero]

theorem n07aAngularBandDerivative_eq_of_weak (m : ℕ) (hm : K.left m < K.right m)
    (n : ℕ) {f g : CanonicalL2 S K m} {k : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g k) :
    n07aAngularBandDerivative m hm n k f = n07aAngularBand m hm n g :=
  n07aAngularWeak_unique m hm (n07aAngularBandDerivative_weak m hm n k f)
    (n07aAngularBand_weak m hm n hfg)

end ContinuousFlexibility.Statements
