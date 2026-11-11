import ContinuousFlexibility.Analysis.OneHighCircleSobolevJetsBasic

/-!
# Sobolev bounds for actual circle derivative families

Every derivative in the family is a continuous function on the physical
circle. Parseval therefore supplies genuine square summability. The exact
derivative multiplier then proves weighted square summability at every
finite order and compares the Bessel norm with physical derivative norms.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal

variable {P : ℝ} [Fact (0 < P)]

theorem circle_norm_frequencyWeighted_nat_le_derivative_endpoints
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s : ℕ) (n : ℤ) :
    ‖frequencyWeighted (circleFrequencyWeight P) (s : ℝ) (fourierCoeff (f 0)) n‖ ≤
      (2 : ℝ) ^ s * (‖fourierCoeff (f 0) n‖ + ‖fourierCoeff (f s) n‖) := by
  rw [circle_norm_frequencyWeighted_nat,
    circle_norm_fourierCoeff_iterated_derivatives f hderiv s n]
  calc
    _ ≤ ((2 : ℝ) ^ s * (1 + |circlePhysicalFrequency P n| ^ s)) *
        ‖fourierCoeff (f 0) n‖ :=
      mul_le_mul_of_nonneg_right (circleFrequencyWeight_nat_pow_le P n s) (norm_nonneg _)
    _ = _ := by ring

/-- All finite Bessel Sobolev norms are genuinely finite for an actual
continuous derivative tower. -/
theorem circle_frequencyWeighted_memLp_of_derivatives
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (f 0))) 2 Measure.count := by
  have h0 := circle_fourier_memLp_two_of_memLp
    (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ (f 0))
  have hs := circle_fourier_memLp_two_of_memLp
    (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ (f s))
  apply (h0.norm.add hs.norm).of_le_mul (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun n => by
    rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact circle_norm_frequencyWeighted_nat_le_derivative_endpoints f hderiv s n

/-- The same finiteness statement at any level of the derivative tower. -/
theorem circle_frequencyWeighted_memLp_of_derivatives_at
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s k : ℕ) :
    MemLp (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
      (fourierCoeff (f k))) 2 Measure.count := by
  have hd : ∀ j : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f (k + j) (y : AddCircle P))
        (f (k + (j + 1)) (x : AddCircle P)) x := by
    intro j x
    simpa only [Nat.add_assoc] using hderiv (k + j) x
  simpa only [Nat.add_zero] using
    circle_frequencyWeighted_memLp_of_derivatives (fun j => f (k + j)) hd s

/-- Every member of a smooth circle derivative tower has absolutely
summable actual Fourier coefficients. -/
theorem circle_fourier_memLp_one_of_derivatives
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (k : ℕ) : MemLp (fourierCoeff (f k)) 1 Measure.count := by
  apply circle_fourier_memLp_one_of_h1
  simpa only [Nat.cast_one] using
    circle_frequencyWeighted_memLp_of_derivatives_at f hderiv 1 k

/-- Each physical derivative of order at most `s` has `L²` norm bounded
by the order-`s` Bessel norm, with constant one. -/
theorem circle_derivative_l2_le_sobolev
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    {k s : ℕ} (hks : k ≤ s) :
    (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal ≤
      circleSobolevNorm (s : ℝ) (f 0) := by
  have hs := circle_frequencyWeighted_memLp_of_derivatives f hderiv s
  have he : eLpNorm (fourierCoeff (f k)) 2 Measure.count ≤
      eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
        (fourierCoeff (f 0))) 2 Measure.count := by
    apply eLpNorm_mono_ae (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun n => by
      rw [circle_norm_frequencyWeighted_nat]
      exact circle_norm_fourierCoeff_derivative_le_weight f hderiv hks n
  rw [← circle_fourier_l2_toReal (f k)]
  exact ENNReal.toReal_mono hs.ne he

/-- The Bessel norm is controlled by the two endpoint physical derivative
norms. This proves the upper equivalence without postulating finiteness. -/
theorem circle_sobolevNorm_le_derivative_endpoints
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    circleSobolevNorm (s : ℝ) (f 0) ≤ (2 : ℝ) ^ s *
      ((eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal +
        (eLpNorm (f s) 2 AddCircle.haarAddCircle).toReal) := by
  have h0 := circle_fourier_memLp_two_of_memLp
    (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ (f 0))
  have hs := circle_fourier_memLp_two_of_memLp
    (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ (f s))
  have he : eLpNorm (frequencyWeighted (circleFrequencyWeight P) (s : ℝ)
        (fourierCoeff (f 0))) 2 Measure.count ≤
      ENNReal.ofReal ((2 : ℝ) ^ s) *
        (eLpNorm (fourierCoeff (f 0)) 2 Measure.count +
          eLpNorm (fourierCoeff (f s)) 2 Measure.count) := by
    calc
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ s) *
          eLpNorm (fun n => ‖fourierCoeff (f 0) n‖ + ‖fourierCoeff (f s) n‖)
            2 Measure.count := by
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (measurable_of_countable _).aestronglyMeasurable
        exact Eventually.of_forall fun n => by
          rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact circle_norm_frequencyWeighted_nat_le_derivative_endpoints f hderiv s n
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ s) *
          (eLpNorm (fun n => ‖fourierCoeff (f 0) n‖) 2 Measure.count +
            eLpNorm (fun n => ‖fourierCoeff (f s) n‖) 2 Measure.count) :=
        mul_le_mul_left' (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)) _
      _ = _ := by
        rw [eLpNorm_norm _ h0.aestronglyMeasurable, eLpNorm_norm _ hs.aestronglyMeasurable]
  have hfinite : ENNReal.ofReal ((2 : ℝ) ^ s) *
      (eLpNorm (fourierCoeff (f 0)) 2 Measure.count +
        eLpNorm (fourierCoeff (f s)) 2 Measure.count) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_lt_top.2 ⟨h0, hs⟩).ne
  have hr := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_add h0.ne hs.ne,
    circle_fourier_l2_toReal (f 0), circle_fourier_l2_toReal (f s)] at hr
  exact hr

/-- Equivalence with the usual sum of physical derivative `L²` norms. -/
theorem circle_sobolevNorm_le_sum_derivative_l2
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    circleSobolevNorm (s : ℝ) (f 0) ≤ (2 : ℝ) ^ (s + 1) *
      ∑ k ∈ Finset.range (s + 1), (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal := by
  have h0 : (eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal ≤
      ∑ k ∈ Finset.range (s + 1), (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal :=
    Finset.single_le_sum (fun k _ => ENNReal.toReal_nonneg)
      (Finset.mem_range.mpr (Nat.zero_lt_succ s))
  have hs : (eLpNorm (f s) 2 AddCircle.haarAddCircle).toReal ≤
      ∑ k ∈ Finset.range (s + 1), (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal :=
    Finset.single_le_sum (fun k _ => ENNReal.toReal_nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self s))
  calc
    _ ≤ (2 : ℝ) ^ s * ((eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal +
        (eLpNorm (f s) 2 AddCircle.haarAddCircle).toReal) :=
      circle_sobolevNorm_le_derivative_endpoints f hderiv s
    _ ≤ (2 : ℝ) ^ s * ((∑ k ∈ Finset.range (s + 1),
        (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal) +
        ∑ k ∈ Finset.range (s + 1), (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add h0 hs) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- The next Sobolev norm is controlled by the zeroth physical norm and
the previous Sobolev norm of the actual first derivative. -/
theorem circle_sobolevNorm_succ_le_l2_add_derivative
    (f : ℕ → C(AddCircle P, ℂ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x)
    (s : ℕ) :
    circleSobolevNorm ((s + 1 : ℕ) : ℝ) (f 0) ≤ (2 : ℝ) ^ (s + 1) *
      ((eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal +
        circleSobolevNorm (s : ℝ) (f 1)) := by
  have hd : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f (k + 1) (y : AddCircle P))
        (f ((k + 1) + 1) (x : AddCircle P)) x :=
    fun k x => hderiv (k + 1) x
  have hlast := circle_derivative_l2_le_sobolev (fun k => f (k + 1)) hd (le_refl s)
  exact (circle_sobolevNorm_le_derivative_endpoints f hderiv (s + 1)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hlast _) (by positivity))

end ContinuousFlexibility.Analysis
