import ContinuousFlexibility.Analysis.N01cCircleLinearVariationBounds

/-!
# Polynomial envelopes for the genuine linear variational equation

The interval has length one after the fixed compact time change. Uniform
pointwise coefficient and forcing bounds therefore control their actual
integrals. The only exponential constant is the already fixed low
coefficient integral. All higher quantities remain polynomial.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

variable {P : ℝ} [Fact (0 < P)]

namespace CircleLinearVariationData

variable (V : CircleLinearVariationData P 0 1)

theorem n01c_coefficientSize_le {A : ℝ} (s : ℕ)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, V.coefficientNorm s t ≤ A) :
    V.coefficientSize s ≤ A := by
  calc
    V.coefficientSize s = ∫ t in (0 : ℝ)..1, V.coefficientNorm s t := rfl
    _ ≤ ∫ _t in (0 : ℝ)..1, A := intervalIntegral.integral_mono_on
      (by norm_num) ((V.coefficientNorm_continuous s).intervalIntegrable_of_Icc
        (by norm_num))
      ((continuous_const : Continuous (fun _ : ℝ => A)).continuousOn.intervalIntegrable_of_Icc (by norm_num)) hA
    _ = A := by simp

theorem n01c_forcingSize_le {A : ℝ} (s : ℕ)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, V.forcingNorm s t ≤ A) :
    V.forcingSize s ≤ A := by
  calc
    V.forcingSize s = ∫ t in (0 : ℝ)..1, V.forcingNorm s t := rfl
    _ ≤ ∫ _t in (0 : ℝ)..1, A := intervalIntegral.integral_mono_on
      (by norm_num) ((V.forcingNorm_continuous s).intervalIntegrable_of_Icc
        (by norm_num))
      ((continuous_const : Continuous (fun _ : ℝ => A)).continuousOn.intervalIntegrable_of_Icc (by norm_num)) hA
    _ = A := by simp

/-- A true angular derivative is controlled by one additional Sobolev
order of the same variation. -/
theorem n01c_angular_value_le_valueNorm (b : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (θ : AddCircle P) :
    |V.value t b θ| ≤ circleSobolevEmbeddingConstant P * V.valueNorm (b + 1) t := by
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  have hpoint := circle_real_norm_apply_le_sobolev_one_of_derivatives
    (V.value t) (V.value_derivative t ht) b θ
  have horder : circleRealSobolevNorm 1 (V.value t b) ≤ V.valueNorm (b + 1) t := by
    simpa only [Nat.add_comm, Nat.cast_one] using
      circle_real_sobolevNorm_derivative_le (V.value t) (V.value_derivative t ht) 1 b
  have hpoint' : |V.value t b θ| ≤
      circleSobolevEmbeddingConstant P * circleRealSobolevNorm 1 (V.value t b) := by
    simpa only [Real.norm_eq_abs] using hpoint
  exact hpoint'.trans (mul_le_mul_of_nonneg_left horder hE)

/-- A linear polynomial envelope: the forcing contains its marked
material weight, while the coefficient does not need a small weight. -/
theorem n01c_sobolev_le_polynomial (s degree : ℕ)
    {A F W U R L t : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hW : 0 ≤ W) (hU : 0 ≤ U) (hR : 1 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) 1) (hL : V.coefficientSize 1 ≤ L)
    (hcoefficient : ∀ r ∈ Icc (0 : ℝ) 1,
      V.coefficientNorm s r ≤ A * U * R)
    (hforcing : ∀ r ∈ Icc (0 : ℝ) 1,
      V.forcingNorm s r ≤ F * W * U * R ^ degree)
    (hforcingLow : ∀ r ∈ Icc (0 : ℝ) 1,
      V.forcingNorm 1 r ≤ F * W * R ^ (degree + 1)) :
    V.valueNorm s t ≤
      circleLinearVariationSobolevConstant P L s * (F + A * F) *
        W * U * R ^ (degree + 2) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hFs := V.n01c_forcingSize_le s hforcing
  have hF1 := V.n01c_forcingSize_le 1 hforcingLow
  have hAs := V.n01c_coefficientSize_le s hcoefficient
  have hpow : R ^ degree ≤ R ^ (degree + 2) :=
    pow_le_pow_right₀ hR (by omega)
  have hfirst : V.forcingSize s ≤ F * W * U * R ^ (degree + 2) :=
    hFs.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hsecond : V.coefficientSize s * V.forcingSize 1 ≤
      A * F * W * U * R ^ (degree + 2) := by
    calc
      _ ≤ (A * U * R) * (F * W * R ^ (degree + 1)) :=
        mul_le_mul hAs hF1 (V.forcingSize_nonneg (by norm_num) 1) (by positivity)
      _ = _ := by
        have he : R ^ (degree + 2) = R ^ (degree + 1) * R := pow_succ R (degree + 1)
        rw [he]
        ring
  have hsum : V.forcingSize s + V.coefficientSize s * V.forcingSize 1 ≤
      (F + A * F) * W * U * R ^ (degree + 2) := by
    calc
      _ ≤ F * W * U * R ^ (degree + 2) +
          A * F * W * U * R ^ (degree + 2) := add_le_add hfirst hsecond
      _ = _ := by ring
  calc
    _ ≤ circleLinearVariationSobolevConstant P L s *
        (V.forcingSize s + V.coefficientSize s * V.forcingSize 1) :=
      V.sobolev_le_of_coefficientSize_le s ht hL
    _ ≤ circleLinearVariationSobolevConstant P L s *
        ((F + A * F) * W * U * R ^ (degree + 2)) :=
      mul_le_mul_of_nonneg_left hsum
        (circleLinearVariationSobolevConstant_pos P L s).le
    _ = _ := by ring

theorem n01c_angular_value_le_polynomial (b degree : ℕ)
    {A F W U R L t : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hW : 0 ≤ W) (hU : 0 ≤ U) (hR : 1 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) 1) (hL : V.coefficientSize 1 ≤ L)
    (hcoefficient : ∀ r ∈ Icc (0 : ℝ) 1,
      V.coefficientNorm (b + 1) r ≤ A * U * R)
    (hforcing : ∀ r ∈ Icc (0 : ℝ) 1,
      V.forcingNorm (b + 1) r ≤ F * W * U * R ^ degree)
    (hforcingLow : ∀ r ∈ Icc (0 : ℝ) 1,
      V.forcingNorm 1 r ≤ F * W * R ^ (degree + 1))
    (θ : AddCircle P) :
    |V.value t b θ| ≤
      (circleSobolevEmbeddingConstant P *
        circleLinearVariationSobolevConstant P L (b + 1) * (F + A * F)) *
          W * U * R ^ (degree + 2) := by
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  calc
    _ ≤ circleSobolevEmbeddingConstant P * V.valueNorm (b + 1) t :=
      V.n01c_angular_value_le_valueNorm b ht θ
    _ ≤ circleSobolevEmbeddingConstant P *
        (circleLinearVariationSobolevConstant P L (b + 1) * (F + A * F) *
          W * U * R ^ (degree + 2)) :=
      mul_le_mul_of_nonneg_left
        (V.n01c_sobolev_le_polynomial (b + 1) degree hA hF hW hU hR
          ht hL hcoefficient hforcing hforcingLow) hE
    _ = _ := by ring

end CircleLinearVariationData

end ContinuousFlexibility.Analysis
