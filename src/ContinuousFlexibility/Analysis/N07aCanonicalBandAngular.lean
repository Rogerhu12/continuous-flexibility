import ContinuousFlexibility.Analysis.N07aCanonicalSeparated

/-!
# The actual sine representative of a differentiated input band

Weak uniqueness identifies the original angular derivatives with their
separated cosine/sine representatives. The radial coefficient remains
the original measurable L² coefficient throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

theorem n07a_referenceAngularBasis_abs_le (n : ℕ) (θ : ℝ) :
    |referenceAngularBasis n θ| ≤ 2 := by
  rw [n07a_referenceAngularBasis_cos, abs_mul, abs_of_nonneg (n07aCosineScale_nonneg n)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (n07aCosineScale_nonneg n)).trans
    (by simpa only [mul_one] using n07aCosineScale_le_two n)

theorem n07aSineBasis_abs_le (n : ℕ) (θ : ℝ) : |n07aSineBasis n θ| ≤ 2 := by
  rw [n07aSineBasis, abs_mul, abs_of_nonneg (n07aCosineScale_nonneg n)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (n07aCosineScale_nonneg n)).trans
    (by simpa only [mul_one] using n07aCosineScale_le_two n)

theorem n07a_referenceAngularBasis_deriv_abs_le (n : ℕ) (θ : ℝ) :
    |deriv (referenceAngularBasis n) θ| ≤ 2 * (2 * (n : ℝ)) := by
  rw [n07a_referenceAngularBasis_deriv, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ))]
  exact (mul_le_mul_of_nonneg_left (n07aSineBasis_abs_le n θ) (by positivity)).trans_eq (mul_comm _ _)

theorem n07a_referenceAngularBasis_second_abs_le (n : ℕ) (θ : ℝ) :
    |deriv (deriv (referenceAngularBasis n)) θ| ≤ 2 * (2 * (n : ℝ)) ^ 2 := by
  rw [deriv_deriv_referenceAngularBasis]
  simp only [Nat.cast_mul, Nat.cast_ofNat, abs_mul, abs_neg, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ))]
  exact (mul_le_mul_of_nonneg_left (n07a_referenceAngularBasis_abs_le n θ)
    (sq_nonneg _)).trans_eq (mul_comm _ _)

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_firstAngular_singleBand_ae (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m} (hu : n07aAngularReflection m u = u)
    (n : ℕ) (hband : n07aAngularBand m hm n u = u)
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 0 1) :
    (d : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => -(2 * (n : ℝ)) * n07aHalfRadialCoefficient u n p.1 * n07aSineBasis n p.2 := by
  have hf := n07aCanonicalRadialCoefficient_memLp u n
  have hg := contDiff_referenceAngularBasis n
  let U := n07aCanonicalSeparated (S := S) hf hg.continuous 2 (n07a_referenceAngularBasis_abs_le n)
  let D := n07aCanonicalSeparated (S := S) hf
    (contDiff_infty_iff_deriv.mp hg).2.continuous (2 * (2 * (n : ℝ)))
    (n07a_referenceAngularBasis_deriv_abs_le n)
  have heU : U = u := by
    apply Lp.ext
    exact (n07aCanonicalSeparated_ae hf hg.continuous 2 (n07a_referenceAngularBasis_abs_le n)).trans
      (by simpa only [hband] using (n07aAngularBand_cosine_ae hm u hu n).symm)
  have hweak : N07aWeakCanonicalMixedDerivative S K m u D 0 1 := by
    have h := n07aCanonicalSeparated_firstAngular (S := S) hf hg (referenceAngularBasis_periodic n)
      2 (2 * (2 * (n : ℝ))) (n07a_referenceAngularBasis_abs_le n)
      (n07a_referenceAngularBasis_deriv_abs_le n)
    change N07aWeakCanonicalMixedDerivative S K m U D 0 1 at h
    rwa [heU] at h
  have heD : D = d := n07a_weakCanonicalMixed_unique hm hweak hd
  rw [← heD]
  filter_upwards [n07aCanonicalSeparated_ae hf (contDiff_infty_iff_deriv.mp hg).2.continuous
    (2 * (2 * (n : ℝ))) (n07a_referenceAngularBasis_deriv_abs_le n)] with p hp
  rw [hp, n07a_referenceAngularBasis_deriv]
  ring

theorem n07a_secondAngular_singleBand_eq (hm : K.left m < K.right m)
    {u dd : CanonicalL2 S K m} (hu : n07aAngularReflection m u = u)
    (n : ℕ) (hband : n07aAngularBand m hm n u = u)
    (hdd : N07aWeakCanonicalMixedDerivative S K m u dd 0 2) :
    dd = -((2 * (n : ℝ)) ^ 2) • u := by
  have hf := n07aCanonicalRadialCoefficient_memLp u n
  have hg := contDiff_referenceAngularBasis n
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hg'p : Function.Periodic (deriv (referenceAngularBasis n)) Real.pi := by
    simpa only [iteratedDeriv_one] using
      circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic n) 1
  let U := n07aCanonicalSeparated (S := S) hf hg.continuous 2 (n07a_referenceAngularBasis_abs_le n)
  let D := n07aCanonicalSeparated (S := S) hf hg'.continuous (2 * (2 * (n : ℝ)))
    (n07a_referenceAngularBasis_deriv_abs_le n)
  let DD := n07aCanonicalSeparated (S := S) hf
    (contDiff_infty_iff_deriv.mp hg').2.continuous (2 * (2 * (n : ℝ)) ^ 2)
    (n07a_referenceAngularBasis_second_abs_le n)
  have heU : U = u := by
    apply Lp.ext
    exact (n07aCanonicalSeparated_ae hf hg.continuous 2 (n07a_referenceAngularBasis_abs_le n)).trans
      (by simpa only [hband] using (n07aAngularBand_cosine_ae hm u hu n).symm)
  have hd : N07aWeakCanonicalMixedDerivative S K m U D 0 1 :=
    n07aCanonicalSeparated_firstAngular hf hg (referenceAngularBasis_periodic n)
      2 (2 * (2 * (n : ℝ))) (n07a_referenceAngularBasis_abs_le n)
      (n07a_referenceAngularBasis_deriv_abs_le n)
  have hd' : N07aWeakCanonicalMixedDerivative S K m D DD 0 1 :=
    n07aCanonicalSeparated_firstAngular hf hg' hg'p
      (2 * (2 * (n : ℝ))) (2 * (2 * (n : ℝ)) ^ 2)
      (n07a_referenceAngularBasis_deriv_abs_le n) (n07a_referenceAngularBasis_second_abs_le n)
  have hUDD : N07aWeakCanonicalMixedDerivative S K m u DD 0 2 := by
    simpa only [heU, Nat.zero_add] using hd.comp hd'
  have heDD : DD = dd := n07a_weakCanonicalMixed_unique hm hUDD hdd
  rw [← heDD]
  apply Lp.ext
  filter_upwards [n07aCanonicalSeparated_ae hf (contDiff_infty_iff_deriv.mp hg').2.continuous
      (2 * (2 * (n : ℝ)) ^ 2) (n07a_referenceAngularBasis_second_abs_le n),
    Lp.coeFn_smul (-((2 * (n : ℝ)) ^ 2)) u,
    n07aAngularBand_cosine_ae hm u hu n] with p hp hs hu₀
  rw [hband] at hu₀
  rw [hp, hs, Pi.smul_apply, smul_eq_mul, hu₀, deriv_deriv_referenceAngularBasis]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

end ContinuousFlexibility.Analysis
