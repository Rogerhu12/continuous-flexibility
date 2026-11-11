import ContinuousFlexibility.Analysis.OneHighCircleSobolevJets

/-!
# Algebra of the physical circle Sobolev norms

These norm estimates retain the actual Fourier/Bessel representation.
Finiteness is either explicit or obtained from an actual continuous
derivative tower. The embedding constant depends only on the fixed period.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem circle_sobolevNorm_nonneg (s : ℝ) (f : AddCircle P → ℂ) :
    0 ≤ circleSobolevNorm s f := ENNReal.toReal_nonneg

/-- Natural-order monotonicity of the physical Bessel norm. -/
theorem circle_sobolevNorm_mono (f : AddCircle P → ℂ) {a b : ℕ} (hab : a ≤ b)
    (hb : MemLp (frequencyWeighted (circleFrequencyWeight P) (b : ℝ)
      (fourierCoeff f)) 2 Measure.count) :
    circleSobolevNorm (a : ℝ) f ≤ circleSobolevNorm (b : ℝ) f := by
  apply ENNReal.toReal_mono hb.ne
  apply eLpNorm_mono_ae (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun n => by
    rw [circle_norm_frequencyWeighted_nat, circle_norm_frequencyWeighted_nat]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (circleFrequencyWeight_one_le P n) hab) (norm_nonneg _)

theorem circle_sobolevNorm_mono_of_derivatives (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    {a b : ℕ} (hab : a ≤ b) :
    circleSobolevNorm (a : ℝ) (f 0) ≤ circleSobolevNorm (b : ℝ) (f 0) :=
  circle_sobolevNorm_mono (f 0) hab
    (circle_frequencyWeighted_memLp_of_derivatives f hderiv b)

/-- Any number of actual derivatives consumes the same number of Bessel
orders, with constant one. -/
theorem circle_sobolevNorm_derivative_le (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s k : ℕ) :
    circleSobolevNorm (s : ℝ) (f k) ≤ circleSobolevNorm ((s + k : ℕ) : ℝ) (f 0) := by
  have hs := circle_frequencyWeighted_memLp_of_derivatives f hderiv (s + k)
  apply ENNReal.toReal_mono hs.ne
  apply eLpNorm_mono_ae (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun n => by
    rw [circle_norm_frequencyWeighted_nat, circle_norm_frequencyWeighted_nat,
      circle_norm_fourierCoeff_iterated_derivatives f hderiv k n, pow_add]
    calc
      _ = (circleFrequencyWeight P n ^ s * |circlePhysicalFrequency P n| ^ k) *
          ‖fourierCoeff (f 0) n‖ := by ring
      _ ≤ (circleFrequencyWeight P n ^ s * circleFrequencyWeight P n ^ k) *
          ‖fourierCoeff (f 0) n‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (abs_circlePhysicalFrequency_le_weight P n) k)
            (pow_nonneg (circleFrequencyWeight_pos P n).le s)) (norm_nonneg _)

theorem circle_sobolevNorm_derivative_le_succ (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    circleSobolevNorm (s : ℝ) (f 1) ≤ circleSobolevNorm ((s + 1 : ℕ) : ℝ) (f 0) :=
  circle_sobolevNorm_derivative_le f hderiv s 1

theorem circle_frequencyWeighted_add (f g : C(AddCircle P, ℂ)) (s : ℝ) :
    frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff (f + g)) =
      frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f) +
        frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g) := by
  have hf : Integrable f AddCircle.haarAddCircle := memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (p := 1) (μ := AddCircle.haarAddCircle) ℂ f)
  have hg : Integrable g AddCircle.haarAddCircle := memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (p := 1) (μ := AddCircle.haarAddCircle) ℂ g)
  have hc := fourierCoeff.add hf hg
  ext n
  rw [frequencyWeighted_apply, ContinuousMap.coe_add, hc]
  simp only [Pi.add_apply, frequencyWeighted_apply, smul_add]

theorem circle_frequencyWeighted_memLp_add (f g : C(AddCircle P, ℂ)) (s : ℝ)
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f)) 2 Measure.count)
    (hg : MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g)) 2 Measure.count) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff (f + g)))
      2 Measure.count := by
  rw [circle_frequencyWeighted_add]
  exact hf.add hg

/-- The triangle inequality for the genuine physical Bessel norm. -/
theorem circle_sobolevNorm_add_le (f g : C(AddCircle P, ℂ)) (s : ℝ)
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f)) 2 Measure.count)
    (hg : MemLp (frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g)) 2 Measure.count) :
    circleSobolevNorm s (f + g) ≤ circleSobolevNorm s f + circleSobolevNorm s g := by
  change (eLpNorm (frequencyWeighted (circleFrequencyWeight P) s
    (fourierCoeff (f + g))) 2 Measure.count).toReal ≤ _
  rw [circle_frequencyWeighted_add]
  have he := ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hf, hg⟩).ne
    (eLpNorm_add_le (f := frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff f))
      (g := frequencyWeighted (circleFrequencyWeight P) s (fourierCoeff g))
      (μ := Measure.count) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa only [circleSobolevNorm, frequencySobolevNorm, ENNReal.toReal_add hf.ne hg.ne] using he

theorem circle_frequencyWeighted_const (s : ℝ) (c : ℂ) :
    frequencyWeighted (circleFrequencyWeight P) s
      (fourierCoeff (fun _ : AddCircle P => c)) = fourierCoeff (fun _ : AddCircle P => c) := by
  have hc : fourierCoeff (fun _ : AddCircle P => c) =
      fun n : ℤ => c * (Pi.single (0 : ℤ) (1 : ℂ) : ℤ → ℂ) n := by
    have hfun : (fun _ : AddCircle P => c) = fun x => c * fourier 0 x := by
      funext x
      rw [fourier_zero, mul_one]
    rw [hfun]
    funext n
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
  funext n
  rw [frequencyWeighted_apply]
  by_cases hn : n = 0
  · subst n
    simp only [circleFrequencyWeight, circlePhysicalFrequency, Int.cast_zero, mul_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_one, Real.one_rpow, one_smul]
  · have hz : fourierCoeff (fun _ : AddCircle P => c) n = 0 := by
      rw [hc]
      simp [Pi.single_apply, hn, Ne.symm hn]
    rw [hz, smul_zero]

theorem circle_frequencyWeighted_memLp_const (s : ℝ) (c : ℂ) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) s
      (fourierCoeff (fun _ : AddCircle P => c))) 2 Measure.count := by
  rw [circle_frequencyWeighted_const]
  exact circle_fourier_memLp_two_of_memLp (memLp_const c)

/-- Normalized Haar measure makes every constant's Sobolev norm its
ordinary complex norm, at every real order. -/
theorem circle_sobolevNorm_const (s : ℝ) (c : ℂ) :
    circleSobolevNorm s (fun _ : AddCircle P => c) = ‖c‖ := by
  change (eLpNorm (frequencyWeighted (circleFrequencyWeight P) s
    (fourierCoeff (fun _ : AddCircle P => c))) 2 Measure.count).toReal = _
  rw [circle_frequencyWeighted_const]
  calc
    _ = (eLpNorm (fun _ : AddCircle P => c) 2 AddCircle.haarAddCircle).toReal := by
      simpa only [frequencySobolevNorm, frequencyWeighted_zero] using
        circle_frequencySobolevNorm_zero_eq_l2 (memLp_const c)
    _ = ‖c‖ := by
      rw [eLpNorm_const' c (by norm_num) (by norm_num)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one]
      rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg c)]

@[simp] theorem circle_sobolevNorm_one (s : ℝ) :
    circleSobolevNorm s (fun _ : AddCircle P => (1 : ℂ)) = 1 := by
  rw [circle_sobolevNorm_const, norm_one]

/-- A positive, explicit embedding constant depending only on the period. -/
def circleSobolevEmbeddingConstant (P : ℝ) : ℝ :=
  max 1 ((eLpNorm (fun n : ℤ => circleFrequencyWeight P n ^ (-1 : ℝ))
    2 Measure.count).toReal)

theorem circleSobolevEmbeddingConstant_one_le (P : ℝ) :
    1 ≤ circleSobolevEmbeddingConstant P := le_max_left _ _

theorem circle_fourierL1Norm_le_sobolev_one {f : AddCircle P → ℂ}
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) 1 (fourierCoeff f))
      2 Measure.count) :
    frequencyL1Norm Measure.count (fourierCoeff f) ≤
      circleSobolevEmbeddingConstant P * circleSobolevNorm 1 f :=
  (circle_fourierL1Norm_le_h1 hf).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (circle_sobolevNorm_nonneg 1 f))

theorem circle_supNorm_le_sobolev_one (f : C(AddCircle P, ℂ))
    (hf : MemLp (frequencyWeighted (circleFrequencyWeight P) 1 (fourierCoeff f))
      2 Measure.count) :
    ‖f‖ ≤ circleSobolevEmbeddingConstant P * circleSobolevNorm 1 f :=
  (circle_supNorm_le_fourierL1Norm f (circle_fourier_memLp_one_of_h1 hf)).trans
    (circle_fourierL1Norm_le_sobolev_one hf)

theorem circle_supNorm_le_sobolev_one_of_derivatives (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (k : ℕ) :
    ‖f k‖ ≤ circleSobolevEmbeddingConstant P * circleSobolevNorm 1 (f k) := by
  apply circle_supNorm_le_sobolev_one
  simpa only [Nat.cast_one] using
    circle_frequencyWeighted_memLp_of_derivatives_at f hderiv 1 k

end ContinuousFlexibility.Analysis
