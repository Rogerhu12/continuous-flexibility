module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowMinkowski
public import ContinuousFlexibility.Analysis.OneHighCircleFlowGronwall
public import ContinuousFlexibility.Analysis.OneHighCircleFourierRealAlgebra

/-!
# One-high Sobolev bounds for the actual linear variational equation

The unknown and source are genuine circle derivative towers.  The time
derivative equation and the zero initial value imply the integral equation;
no norm inequality is an input.  Sobolev multiplication first closes the
low H¹ estimate and then gives every high-order estimate with only one
high coefficient or forcing norm.  The exponential constant contains
only the time integral of the coefficient's H¹ norm.

This is the linear equation used by each positive state-parameter
variation of the ordinary flow, after the highest variation has been
separated from its actual lower-order forcing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

variable {P : ℝ} [Fact (0 < P)]

/-- Actual angular towers and their actual linear time equation.  The
source tower is identified at order zero with coefficient times unknown
plus forcing; its derivative clauses identify every higher angular jet. -/
structure CircleLinearVariationData (P a b : ℝ) where
  value : ℝ → ℕ → C(AddCircle P, ℝ)
  coefficient : ℝ → ℕ → C(AddCircle P, ℝ)
  forcing : ℝ → ℕ → C(AddCircle P, ℝ)
  source : ℝ → ℕ → C(AddCircle P, ℝ)
  value_derivative : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
    HasDerivAt (fun η : ℝ => value t n (η : AddCircle P))
      (value t (n + 1) (θ : AddCircle P)) θ
  coefficient_derivative : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
    HasDerivAt (fun η : ℝ => coefficient t n (η : AddCircle P))
      (coefficient t (n + 1) (θ : AddCircle P)) θ
  forcing_derivative : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
    HasDerivAt (fun η : ℝ => forcing t n (η : AddCircle P))
      (forcing t (n + 1) (θ : AddCircle P)) θ
  source_derivative : ∀ t ∈ Icc a b, ∀ n : ℕ, ∀ θ : ℝ,
    HasDerivAt (fun η : ℝ => source t n (η : AddCircle P))
      (source t (n + 1) (θ : AddCircle P)) θ
  value_continuous : ∀ n, ContinuousOn (fun t => value t n) (Icc a b)
  coefficient_continuous : ∀ n, ContinuousOn (fun t => coefficient t n) (Icc a b)
  forcing_continuous : ∀ n, ContinuousOn (fun t => forcing t n) (Icc a b)
  source_continuous : ∀ n, ContinuousOn (fun t => source t n) (Icc a b)
  initial : ∀ n, value a n = 0
  equation : ∀ t ∈ Ioo a b, ∀ n : ℕ, ∀ θ : AddCircle P,
    HasDerivAt (fun r => value r n θ) (source t n θ) t
  source_eq : ∀ t ∈ Icc a b,
    source t 0 = coefficient t 0 * value t 0 + forcing t 0

/-- This coefficient comes only from Sobolev Minkowski, multiplication,
and the fixed circle H¹ embedding constant. -/
def circleLinearVariationKernelConstant (P : ℝ) (s : ℕ) : ℝ :=
  (2 : ℝ) ^ (s + 1) * (1 + (2 : ℝ) ^ s * circleSobolevEmbeddingConstant P)

theorem circleLinearVariationKernelConstant_pos (P : ℝ) (s : ℕ) :
    0 < circleLinearVariationKernelConstant P s := by
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  dsimp only [circleLinearVariationKernelConstant]
  positivity

/-- Only the low coefficient integral enters this high-order constant. -/
def circleLinearVariationSobolevConstant (P L : ℝ) (s : ℕ) : ℝ :=
  circleLinearVariationKernelConstant P s *
    Real.exp (circleLinearVariationKernelConstant P s * L) *
    max 1 (circleLinearVariationKernelConstant P 1 *
      Real.exp (2 * circleLinearVariationKernelConstant P 1 * L))

theorem circleLinearVariationSobolevConstant_pos (P L : ℝ) (s : ℕ) :
    0 < circleLinearVariationSobolevConstant P L s := by
  have hK := circleLinearVariationKernelConstant_pos P s
  have hM : 0 < max 1 (circleLinearVariationKernelConstant P 1 *
      Real.exp (2 * circleLinearVariationKernelConstant P 1 * L)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  exact mul_pos (mul_pos hK (Real.exp_pos _)) hM

theorem circleLinearVariationSobolevConstant_mono (P : ℝ) (s : ℕ) :
    Monotone (fun L => circleLinearVariationSobolevConstant P L s) := by
  intro L M hLM
  have hK : 0 ≤ circleLinearVariationKernelConstant P s :=
    (circleLinearVariationKernelConstant_pos P s).le
  have hK₁ : 0 ≤ circleLinearVariationKernelConstant P 1 :=
    (circleLinearVariationKernelConstant_pos P 1).le
  have hs := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLM hK)
  have h₁ := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hLM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK₁))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hs hK)
    (max_le_max le_rfl (mul_le_mul_of_nonneg_left h₁ hK₁))
    (zero_le_one.trans (le_max_left _ _)) (mul_nonneg hK (Real.exp_pos _).le)

private theorem circleLinear_product_memLp (A Y : ℕ → C(AddCircle P, ℝ))
    (hA : ∀ n : ℕ, ∀ θ : ℝ, HasDerivAt
      (fun η : ℝ => A n (η : AddCircle P)) (A (n + 1) (θ : AddCircle P)) θ)
    (hY : ∀ n : ℕ, ∀ θ : ℝ, HasDerivAt
      (fun η : ℝ => Y n (η : AddCircle P)) (Y (n + 1) (θ : AddCircle P)) θ)
    (s : ℕ) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (circleComplexify (A 0 * Y 0)))) 2 Measure.count := by
  have h := circle_frequencyWeighted_mul_memLp s
    (circleComplexify (A 0)) (circleComplexify (Y 0))
    (circle_fourier_memLp_one_of_derivatives (fun n => circleComplexify (A n))
      (circleComplexify_hasDerivAt A hA) 0)
    (circle_fourier_memLp_one_of_derivatives (fun n => circleComplexify (Y n))
      (circleComplexify_hasDerivAt Y hY) 0)
    (circle_frequencyWeighted_memLp_of_derivatives (fun n => circleComplexify (A n))
      (circleComplexify_hasDerivAt A hA) s)
    (circle_frequencyWeighted_memLp_of_derivatives (fun n => circleComplexify (Y n))
      (circleComplexify_hasDerivAt Y hY) s)
  simpa only [circleComplexify_mul] using h

omit [Fact (0 < P)] in
private theorem circleLinear_source_absorb (C X F : ℝ)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hF : 0 ≤ F) :
    C * X + F ≤ (1 + C) * (X + F) := by
  nlinarith [mul_nonneg hC hF]

omit [Fact (0 < P)] in
private theorem circleLinear_source_combine
    (C M A1 As Y1 Ys F AL YL R Z : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hA1 : 0 ≤ A1) (hAs : 0 ≤ As)
    (hY1 : 0 ≤ Y1) (hYs : 0 ≤ Ys) (hF : 0 ≤ F)
    (hZ : Z ≤ R + F) (hR : R ≤ C * (As * YL + AL * Ys))
    (hAL : AL ≤ M * A1) (hYL : YL ≤ M * Y1) :
    Z ≤ (1 + C * M) * (A1 * Ys + As * Y1 + F) := by
  calc
    Z ≤ C * (As * YL + AL * Ys) + F := hZ.trans (add_le_add hR le_rfl)
    _ ≤ C * (As * (M * Y1) + (M * A1) * Ys) + F :=
      add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hYL hAs)
          (mul_le_mul_of_nonneg_right hAL hYs)) hC) le_rfl
    _ = (C * M) * (A1 * Ys + As * Y1) + F := by ring
    _ ≤ _ := circleLinear_source_absorb _ _ _ (mul_nonneg hC hM)
      (add_nonneg (mul_nonneg hA1 hYs) (mul_nonneg hAs hY1)) hF

private theorem circleLinear_source_norm (A Y F : ℕ → C(AddCircle P, ℝ))
    (hA : ∀ n : ℕ, ∀ θ : ℝ, HasDerivAt
      (fun η : ℝ => A n (η : AddCircle P)) (A (n + 1) (θ : AddCircle P)) θ)
    (hY : ∀ n : ℕ, ∀ θ : ℝ, HasDerivAt
      (fun η : ℝ => Y n (η : AddCircle P)) (Y (n + 1) (θ : AddCircle P)) θ)
    (hF : ∀ n : ℕ, ∀ θ : ℝ, HasDerivAt
      (fun η : ℝ => F n (η : AddCircle P)) (F (n + 1) (θ : AddCircle P)) θ)
    (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (A 0 * Y 0 + F 0) ≤
      (1 + (2 : ℝ) ^ s * circleSobolevEmbeddingConstant P) *
        (circleRealSobolevNorm 1 (A 0) * circleRealSobolevNorm (s : ℝ) (Y 0) +
          circleRealSobolevNorm (s : ℝ) (A 0) * circleRealSobolevNorm 1 (Y 0) +
          circleRealSobolevNorm (s : ℝ) (F 0)) := by
  exact circleLinear_source_combine ((2 : ℝ) ^ s) (circleSobolevEmbeddingConstant P)
    (circleRealSobolevNorm 1 (A 0)) (circleRealSobolevNorm (s : ℝ) (A 0))
    (circleRealSobolevNorm 1 (Y 0)) (circleRealSobolevNorm (s : ℝ) (Y 0))
    (circleRealSobolevNorm (s : ℝ) (F 0))
    (circleRealFourierL1Norm (A 0)) (circleRealFourierL1Norm (Y 0))
    (circleRealSobolevNorm (s : ℝ) (A 0 * Y 0))
    (circleRealSobolevNorm (s : ℝ) (A 0 * Y 0 + F 0))
    (by positivity) (zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P))
    (circle_real_sobolevNorm_nonneg _ _) (circle_real_sobolevNorm_nonneg _ _)
    (circle_real_sobolevNorm_nonneg _ _) (circle_real_sobolevNorm_nonneg _ _)
    (circle_real_sobolevNorm_nonneg _ _)
    (circle_real_sobolevNorm_add_le _ _ _ (circleLinear_product_memLp A Y hA hY s)
      (circle_frequencyWeighted_memLp_of_derivatives (fun n => circleComplexify (F n))
        (circleComplexify_hasDerivAt F hF) s))
    (circle_real_sobolevNorm_mul_le_of_derivatives A Y hA hY s)
    (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives A hA 0)
    (circle_real_fourierL1Norm_le_sobolev_one_of_derivatives Y hY 0)

namespace CircleLinearVariationData

variable {a b : ℝ} (V : CircleLinearVariationData P a b)

def valueNorm (s : ℕ) (t : ℝ) : ℝ :=
  circleRealSobolevNorm (s : ℝ) (V.value t 0)

def coefficientNorm (s : ℕ) (t : ℝ) : ℝ :=
  circleRealSobolevNorm (s : ℝ) (V.coefficient t 0)

def forcingNorm (s : ℕ) (t : ℝ) : ℝ :=
  circleRealSobolevNorm (s : ℝ) (V.forcing t 0)

def coefficientSize (s : ℕ) : ℝ := ∫ r in a..b, V.coefficientNorm s r

def forcingSize (s : ℕ) : ℝ := ∫ r in a..b, V.forcingNorm s r

theorem valueNorm_nonneg (s : ℕ) (t : ℝ) : 0 ≤ V.valueNorm s t :=
  circle_real_sobolevNorm_nonneg _ _

theorem coefficientNorm_nonneg (s : ℕ) (t : ℝ) : 0 ≤ V.coefficientNorm s t :=
  circle_real_sobolevNorm_nonneg _ _

theorem forcingNorm_nonneg (s : ℕ) (t : ℝ) : 0 ≤ V.forcingNorm s t :=
  circle_real_sobolevNorm_nonneg _ _

theorem valueNorm_continuous (s : ℕ) :
    ContinuousOn (V.valueNorm s) (Icc a b) :=
  continuousOn_circleRealSobolevNorm_of_derivatives V.value V.value_derivative s
    (V.value_continuous 0) (V.value_continuous s)

theorem coefficientNorm_continuous (s : ℕ) :
    ContinuousOn (V.coefficientNorm s) (Icc a b) :=
  continuousOn_circleRealSobolevNorm_of_derivatives V.coefficient V.coefficient_derivative s
    (V.coefficient_continuous 0) (V.coefficient_continuous s)

theorem forcingNorm_continuous (s : ℕ) :
    ContinuousOn (V.forcingNorm s) (Icc a b) :=
  continuousOn_circleRealSobolevNorm_of_derivatives V.forcing V.forcing_derivative s
    (V.forcing_continuous 0) (V.forcing_continuous s)

theorem coefficientSize_nonneg (hab : a ≤ b) (s : ℕ) :
    0 ≤ V.coefficientSize s :=
  intervalIntegral.integral_nonneg hab (fun r _ => V.coefficientNorm_nonneg s r)

theorem forcingSize_nonneg (hab : a ≤ b) (s : ℕ) :
    0 ≤ V.forcingSize s :=
  intervalIntegral.integral_nonneg hab (fun r _ => V.forcingNorm_nonneg s r)

theorem coefficientSize_partial_le {t : ℝ} (ht : t ∈ Icc a b) (s : ℕ) :
    (∫ r in a..t, V.coefficientNorm s r) ≤ V.coefficientSize s :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Eventually.of_forall (fun r => V.coefficientNorm_nonneg s r))
    ((V.coefficientNorm_continuous s).intervalIntegrable_of_Icc (ht.1.trans ht.2))

theorem forcingSize_partial_le {t : ℝ} (ht : t ∈ Icc a b) (s : ℕ) :
    (∫ r in a..t, V.forcingNorm s r) ≤ V.forcingSize s :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Eventually.of_forall (fun r => V.forcingNorm_nonneg s r))
    ((V.forcingNorm_continuous s).intervalIntegrable_of_Icc (ht.1.trans ht.2))

/-- The scalar fundamental theorem gives the actual equation for every
angular jet, including both endpoints of the supplied interval. -/
theorem integral_eq {t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (θ : AddCircle P) :
    V.value t n θ = ∫ r in a..t, V.source r n θ := by
  have hy : ContinuousOn (fun r => V.value r n θ) (Icc a b) :=
    (ContinuousMap.evalCLM ℝ θ).continuous.comp_continuousOn (V.value_continuous n)
  have hs : ContinuousOn (fun r => V.source r n θ) (Icc a b) :=
    (ContinuousMap.evalCLM ℝ θ).continuous.comp_continuousOn (V.source_continuous n)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hy.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r hr => V.equation r ⟨hr.1, hr.2.trans_le ht.2⟩ n θ)
    ((hs.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
  rw [V.initial n, ContinuousMap.zero_apply, sub_zero] at hFTC
  exact hFTC.symm

/-- Actual Sobolev multiplication separates the high coefficient and
the high unknown.  The remaining source norm is the actual forcing. -/
theorem sourceNorm_le (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    circleRealSobolevNorm (s : ℝ) (V.source t 0) ≤
      (1 + (2 : ℝ) ^ s * circleSobolevEmbeddingConstant P) *
        (V.coefficientNorm 1 t * V.valueNorm s t +
          V.coefficientNorm s t * V.valueNorm 1 t + V.forcingNorm s t) := by
  rw [V.source_eq t ht]
  simpa only [valueNorm, coefficientNorm, forcingNorm, Nat.cast_one] using
    circleLinear_source_norm (V.coefficient t) (V.value t) (V.forcing t)
      (V.coefficient_derivative t ht) (V.value_derivative t ht) (V.forcing_derivative t ht) s

/-- The norm integral inequality is derived from the true time equation. -/
theorem sobolev_integral_le (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    V.valueNorm s t ≤ ∫ r in a..t, circleLinearVariationKernelConstant P s *
      (V.coefficientNorm 1 r * V.valueNorm s r +
        V.coefficientNorm s r * V.valueNorm 1 r + V.forcingNorm s r) := by
  let c : ℝ := 1 + (2 : ℝ) ^ s * circleSobolevEmbeddingConstant P
  let f : ℝ → ℝ := fun r =>
    V.coefficientNorm 1 r * V.valueNorm s r +
      V.coefficientNorm s r * V.valueNorm 1 r + V.forcingNorm s r
  have hsource : ContinuousOn
      (fun r => circleRealSobolevNorm (s : ℝ) (V.source r 0)) (Icc a b) :=
    continuousOn_circleRealSobolevNorm_of_derivatives V.source V.source_derivative s
      (V.source_continuous 0) (V.source_continuous s)
  have hf : ContinuousOn f (Icc a b) :=
    (((V.coefficientNorm_continuous 1).mul (V.valueNorm_continuous s)).add
      ((V.coefficientNorm_continuous s).mul (V.valueNorm_continuous 1))).add
      (V.forcingNorm_continuous s)
  have hcf : ContinuousOn (fun r => c * f r) (Icc a b) :=
    continuousOn_const.mul hf
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht.1
    ((hsource.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    ((hcf.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    (fun r hr => V.sourceNorm_le s ⟨hr.1, hr.2.trans ht.2⟩)
  have hM := circle_real_sobolevNorm_intervalIntegral_le
    (V.value t) V.source ht.1 (V.value_derivative t ht)
    (fun r hr => V.source_derivative r ⟨hr.1, hr.2.trans ht.2⟩)
    (fun n => (V.source_continuous n).mono (Icc_subset_Icc le_rfl ht.2))
    (V.integral_eq ht) s
  calc
    V.valueNorm s t ≤ (2 : ℝ) ^ (s + 1) *
        ∫ r in a..t, circleRealSobolevNorm (s : ℝ) (V.source r 0) := hM
    _ ≤ (2 : ℝ) ^ (s + 1) * ∫ r in a..t, c * f r :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by
      simp only [intervalIntegral.integral_const_mul, circleLinearVariationKernelConstant, c, f]
      ring

/-- The low-order solution estimate uses only the actual H¹ integrals. -/
theorem low_sobolev_le {t : ℝ} (ht : t ∈ Icc a b) :
    V.valueNorm 1 t ≤ circleLinearVariationKernelConstant P 1 * V.forcingSize 1 *
      Real.exp (2 * circleLinearVariationKernelConstant P 1 * V.coefficientSize 1) := by
  let K : ℝ := circleLinearVariationKernelConstant P 1
  have hK : 0 ≤ K := (circleLinearVariationKernelConstant_pos P 1).le
  have hlin (τ : ℝ) (hτ : τ ∈ Icc a t) :
      V.valueNorm 1 τ ≤ 0 + ∫ r in a..τ,
        (2 * K * V.coefficientNorm 1 r) * V.valueNorm 1 r + K * V.forcingNorm 1 r := by
    have hh := V.sobolev_integral_le 1 ⟨hτ.1, hτ.2.trans ht.2⟩
    rw [zero_add]
    apply hh.trans_eq
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [K]
    ring
  have hgronwall := integral_gronwall_of_continuousOn ht.1
    ((V.valueNorm_continuous 1).mono (Icc_subset_Icc le_rfl ht.2))
    ((continuousOn_const.mul (V.coefficientNorm_continuous 1)).mono
      (Icc_subset_Icc le_rfl ht.2))
    ((continuousOn_const.mul (V.forcingNorm_continuous 1)).mono
      (Icc_subset_Icc le_rfl ht.2))
    (fun r _ => mul_nonneg (mul_nonneg (by positivity) hK) (V.coefficientNorm_nonneg 1 r))
    (fun r _ => mul_nonneg hK (V.forcingNorm_nonneg 1 r)) hlin
  have hexp : Real.exp (2 * K * ∫ r in a..t, V.coefficientNorm 1 r) ≤
      Real.exp (2 * K * V.coefficientSize 1) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (V.coefficientSize_partial_le ht 1)
      (mul_nonneg (by positivity) hK))
  calc
    V.valueNorm 1 t ≤ (K * ∫ r in a..t, V.forcingNorm 1 r) *
        Real.exp (2 * K * ∫ r in a..t, V.coefficientNorm 1 r) := by
      simpa only [zero_add, Pi.mul_def, Pi.mul_apply,
        intervalIntegral.integral_const_mul] using hgronwall
    _ ≤ (K * V.forcingSize 1) * Real.exp (2 * K * V.coefficientSize 1) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (V.forcingSize_partial_le ht 1) hK) hexp
        (Real.exp_pos _).le (mul_nonneg hK (V.forcingSize_nonneg (ht.1.trans ht.2) 1))

/-- The actual linear equation has one high coefficient or forcing norm.
All orders share the same low integral in the explicit constant. -/
theorem sobolev_le (s : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    V.valueNorm s t ≤
      circleLinearVariationSobolevConstant P (V.coefficientSize 1) s *
        (V.forcingSize s + V.coefficientSize s * V.forcingSize 1) := by
  let K : ℝ := circleLinearVariationKernelConstant P s
  let K₁ : ℝ := circleLinearVariationKernelConstant P 1
  let L : ℝ := V.coefficientSize 1
  let R : ℝ := K₁ * V.forcingSize 1 * Real.exp (2 * K₁ * L)
  have hab : a ≤ b := ht.1.trans ht.2
  have hK : 0 ≤ K := (circleLinearVariationKernelConstant_pos P s).le
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (circleLinearVariationKernelConstant_pos P 1).le
      (V.forcingSize_nonneg hab 1)) (Real.exp_pos _).le
  have hsource : ContinuousOn
      (fun r => K * (V.coefficientNorm s r * R + V.forcingNorm s r)) (Icc a b) :=
    continuousOn_const.mul (((V.coefficientNorm_continuous s).mul continuousOn_const).add
      (V.forcingNorm_continuous s))
  have hlin (τ : ℝ) (hτ : τ ∈ Icc a t) :
      V.valueNorm s τ ≤ 0 + ∫ r in a..τ,
        (K * V.coefficientNorm 1 r) * V.valueNorm s r +
          K * (V.coefficientNorm s r * R + V.forcingNorm s r) := by
    have hτab : τ ∈ Icc a b := ⟨hτ.1, hτ.2.trans ht.2⟩
    have hleft : ContinuousOn (fun r => K *
        (V.coefficientNorm 1 r * V.valueNorm s r +
          V.coefficientNorm s r * V.valueNorm 1 r + V.forcingNorm s r)) (Icc a b) :=
      continuousOn_const.mul
        ((((V.coefficientNorm_continuous 1).mul (V.valueNorm_continuous s)).add
          ((V.coefficientNorm_continuous s).mul (V.valueNorm_continuous 1))).add
          (V.forcingNorm_continuous s))
    have hright : ContinuousOn (fun r =>
        (K * V.coefficientNorm 1 r) * V.valueNorm s r +
          K * (V.coefficientNorm s r * R + V.forcingNorm s r)) (Icc a b) :=
      (((continuousOn_const.mul (V.coefficientNorm_continuous 1)).mul
        (V.valueNorm_continuous s)).add hsource)
    rw [zero_add]
    apply (V.sobolev_integral_le s hτab).trans
    apply intervalIntegral.integral_mono_on (μ := volume) hτ.1
      ((hleft.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1)
      ((hright.mono (Icc_subset_Icc le_rfl hτab.2)).intervalIntegrable_of_Icc hτ.1)
    intro r hr
    have hlow : V.valueNorm 1 r ≤ R :=
      V.low_sobolev_le ⟨hr.1, hr.2.trans hτab.2⟩
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add_right (add_le_add_left
        (mul_le_mul_of_nonneg_left hlow (V.coefficientNorm_nonneg s r))
        (V.coefficientNorm 1 r * V.valueNorm s r)) (V.forcingNorm s r)) hK
    convert hh using 1 <;> ring
  have hg := integral_gronwall_of_continuousOn ht.1
    ((V.valueNorm_continuous s).mono (Icc_subset_Icc le_rfl ht.2))
    ((continuousOn_const.mul (V.coefficientNorm_continuous 1)).mono
      (Icc_subset_Icc le_rfl ht.2))
    (hsource.mono (Icc_subset_Icc le_rfl ht.2))
    (fun r _ => mul_nonneg hK (V.coefficientNorm_nonneg 1 r))
    (fun r _ => mul_nonneg hK
      (add_nonneg (mul_nonneg (V.coefficientNorm_nonneg s r) hR)
        (V.forcingNorm_nonneg s r))) hlin
  have hAI : IntervalIntegrable (V.coefficientNorm s) volume a t :=
    ((V.coefficientNorm_continuous s).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hFI : IntervalIntegrable (V.forcingNorm s) volume a t :=
    ((V.forcingNorm_continuous s).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hfactor :
      K * ((∫ r in a..t, V.coefficientNorm s r) * R +
        ∫ r in a..t, V.forcingNorm s r) ≤
      K * (V.coefficientSize s * R + V.forcingSize s) :=
    mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_right (V.coefficientSize_partial_le ht s) hR)
        (V.forcingSize_partial_le ht s)) hK
  have hexp : Real.exp (K * ∫ r in a..t, V.coefficientNorm 1 r) ≤
      Real.exp (K * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (V.coefficientSize_partial_le ht 1) hK)
  have hraw : V.valueNorm s t ≤
      (K * (V.coefficientSize s * R + V.forcingSize s)) * Real.exp (K * L) := by
    have hg' : V.valueNorm s t ≤
        (K * ((∫ r in a..t, V.coefficientNorm s r) * R +
          ∫ r in a..t, V.forcingNorm s r)) *
            Real.exp (K * ∫ r in a..t, V.coefficientNorm 1 r) := by
      simpa only [zero_add, Pi.mul_def, Pi.mul_apply,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hAI.mul_const R) hFI,
        intervalIntegral.integral_mul_const] using hg
    exact hg'.trans (mul_le_mul hfactor hexp (Real.exp_pos _).le
      (mul_nonneg hK (add_nonneg
        (mul_nonneg (V.coefficientSize_nonneg hab s) hR) (V.forcingSize_nonneg hab s))))
  let M : ℝ := max 1 (K₁ * Real.exp (2 * K₁ * L))
  have hsplit : V.forcingSize s +
      (K₁ * Real.exp (2 * K₁ * L)) * (V.coefficientSize s * V.forcingSize 1) ≤
      M * (V.forcingSize s + V.coefficientSize s * V.forcingSize 1) := by
    calc
      _ ≤ M * V.forcingSize s + M * (V.coefficientSize s * V.forcingSize 1) :=
        add_le_add
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left
            1 (K₁ * Real.exp (2 * K₁ * L))) (V.forcingSize_nonneg hab s))
          (mul_le_mul_of_nonneg_right (le_max_right 1 (K₁ * Real.exp (2 * K₁ * L)))
            (mul_nonneg (V.coefficientSize_nonneg hab s) (V.forcingSize_nonneg hab 1)))
      _ = _ := by ring
  calc
    V.valueNorm s t ≤ (K * (V.coefficientSize s * R + V.forcingSize s)) *
        Real.exp (K * L) := hraw
    _ = (K * Real.exp (K * L)) *
        (V.forcingSize s + (K₁ * Real.exp (2 * K₁ * L)) *
          (V.coefficientSize s * V.forcingSize 1)) := by dsimp only [R]; ring
    _ ≤ (K * Real.exp (K * L)) *
        (M * (V.forcingSize s + V.coefficientSize s * V.forcingSize 1)) :=
      mul_le_mul_of_nonneg_left hsplit (mul_nonneg hK (Real.exp_pos _).le)
    _ = _ := by
      dsimp only [circleLinearVariationSobolevConstant, K, K₁, L, M]
      ring

/-- A uniform low coefficient bound gives a uniform high-order
constant, without placing any high norm of the state in that constant. -/
theorem sobolev_le_of_coefficientSize_le (s : ℕ) {t L : ℝ}
    (ht : t ∈ Icc a b) (hL : V.coefficientSize 1 ≤ L) :
    V.valueNorm s t ≤ circleLinearVariationSobolevConstant P L s *
      (V.forcingSize s + V.coefficientSize s * V.forcingSize 1) :=
  (V.sobolev_le s ht).trans (mul_le_mul_of_nonneg_right
    (circleLinearVariationSobolevConstant_mono P s hL)
    (add_nonneg (V.forcingSize_nonneg (ht.1.trans ht.2) s)
      (mul_nonneg (V.coefficientSize_nonneg (ht.1.trans ht.2) s)
        (V.forcingSize_nonneg (ht.1.trans ht.2) 1))))

/-- Pointwise angular jets cost one fixed Sobolev order, independently
of the state-parameter order that produced this variational equation. -/
theorem angular_value_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc a b) (θ : AddCircle P) :
    |V.value t n θ| ≤ circleSobolevEmbeddingConstant P *
      circleLinearVariationSobolevConstant P (V.coefficientSize 1) (n + 1) *
        (V.forcingSize (n + 1) + V.coefficientSize (n + 1) * V.forcingSize 1) := by
  have hpoint := circle_real_norm_apply_le_sobolev_one_of_derivatives
    (V.value t) (V.value_derivative t ht) n θ
  have horder : circleRealSobolevNorm 1 (V.value t n) ≤ V.valueNorm (n + 1) t := by
    simpa only [valueNorm, Nat.add_comm, Nat.cast_one] using
      circle_real_sobolevNorm_derivative_le (V.value t) (V.value_derivative t ht) 1 n
  have hE : 0 ≤ circleSobolevEmbeddingConstant P :=
    zero_le_one.trans (circleSobolevEmbeddingConstant_one_le P)
  calc
    |V.value t n θ| ≤ circleSobolevEmbeddingConstant P *
        circleRealSobolevNorm 1 (V.value t n) := by
      simpa only [Real.norm_eq_abs] using hpoint
    _ ≤ circleSobolevEmbeddingConstant P * V.valueNorm (n + 1) t :=
      mul_le_mul_of_nonneg_left horder hE
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (V.sobolev_le (n + 1) ht) hE

end CircleLinearVariationData

end ContinuousFlexibility.Analysis
