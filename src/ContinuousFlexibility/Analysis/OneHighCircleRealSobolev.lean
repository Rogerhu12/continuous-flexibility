import ContinuousFlexibility.Analysis.OneHighCircleFourierDerivativeProducts
import ContinuousFlexibility.Analysis.OneHighPeriodicJets
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The same physical circle Sobolev norms for real functions

Real functions are included in the complex Fourier representation by the
canonical real inclusion. No separate Fourier transform or Sobolev norm is
introduced. The derivative-product and derivative-norm estimates therefore
apply directly to real composition formulas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

/-- Canonical complexification of a real continuous circle function. -/
def circleComplexify (f : C(AddCircle P, ℝ)) : C(AddCircle P, ℂ) :=
  ⟨fun θ => (f θ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem circleComplexify_apply (f : C(AddCircle P, ℝ)) (θ : AddCircle P) :
    circleComplexify f θ = (f θ : ℂ) := rfl

/-- Notation for the existing physical Fourier norm of a real function. -/
abbrev circleRealSobolevNorm (s : ℝ) (f : C(AddCircle P, ℝ)) : ℝ :=
  circleSobolevNorm s (circleComplexify f)

abbrev circleRealFourierL1Norm (f : C(AddCircle P, ℝ)) : ℝ :=
  frequencyL1Norm Measure.count (fourierCoeff (circleComplexify f))

theorem circle_eLpNorm_complexify (f : C(AddCircle P, ℝ)) (p : ℝ≥0∞) :
    eLpNorm (circleComplexify f) p AddCircle.haarAddCircle =
      eLpNorm f p AddCircle.haarAddCircle := by
  apply eLpNorm_congr_norm_ae (circleComplexify f).continuous.aestronglyMeasurable
    f.continuous.aestronglyMeasurable
  exact Eventually.of_forall fun θ => by simp

theorem circle_real_sobolevNorm_zero_eq_l2 (f : C(AddCircle P, ℝ)) :
    circleRealSobolevNorm 0 f = (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  simpa only [circle_eLpNorm_complexify] using
    circle_frequencySobolevNorm_zero_eq_l2
      (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℂ (circleComplexify f))

theorem circleComplexify_hasDerivAt
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => circleComplexify (f k) (y : AddCircle P))
      (circleComplexify (f (k + 1)) (x : AddCircle P)) x :=
  (hderiv k x).ofReal_comp

theorem circle_real_sobolevNorm_le_derivative_endpoints
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (f 0) ≤ (2 : ℝ) ^ s *
      ((eLpNorm (f 0) 2 AddCircle.haarAddCircle).toReal +
        (eLpNorm (f s) 2 AddCircle.haarAddCircle).toReal) := by
  simpa only [circle_eLpNorm_complexify] using
    circle_sobolevNorm_le_derivative_endpoints
      (fun k => circleComplexify (f k)) (circleComplexify_hasDerivAt f hderiv) s

theorem circle_real_derivative_l2_le_sobolev
    (f : ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ k : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f k (y : AddCircle P))
        (f (k + 1) (x : AddCircle P)) x) {k s : ℕ} (hks : k ≤ s) :
    (eLpNorm (f k) 2 AddCircle.haarAddCircle).toReal ≤
      circleRealSobolevNorm (s : ℝ) (f 0) := by
  simpa only [circle_eLpNorm_complexify] using
    circle_derivative_l2_le_sobolev
      (fun k => circleComplexify (f k)) (circleComplexify_hasDerivAt f hderiv) hks

/-- The full distributed-derivative estimate for real functions, with
their actual complex Fourier coefficients and no extra summability premise. -/
theorem circle_real_derivative_product_oneHigh (k s : ℕ)
    (f : Fin (k + 1) → ℕ → C(AddCircle P, ℝ))
    (hderiv : ∀ i, ∀ j : ℕ, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => f i j (y : AddCircle P))
        (f i (j + 1) (x : AddCircle P)) x)
    (a : Fin (k + 1) → ℕ) (ha : ∑ i, a i ≤ s) :
    (eLpNorm (∏ i, f i (a i)) 2 AddCircle.haarAddCircle).toReal ≤
      ∑ j, circleRealSobolevNorm (s : ℝ) (f j 0) *
        ∏ i ∈ Finset.univ.erase j, circleRealFourierL1Norm (f i 0) := by
  have h := circle_derivative_product_oneHigh k s
    (fun i j => circleComplexify (f i j))
    (fun i => circleComplexify_hasDerivAt (f i) (hderiv i)) a ha
  have he : eLpNorm (∏ i, circleComplexify (f i (a i))) 2 AddCircle.haarAddCircle =
      eLpNorm (∏ i, f i (a i)) 2 AddCircle.haarAddCircle := by
    apply eLpNorm_congr_norm_ae
      (∏ i, circleComplexify (f i (a i))).continuous.aestronglyMeasurable
      (∏ i, f i (a i)).continuous.aestronglyMeasurable
    exact Eventually.of_forall fun θ => by simp [norm_prod]
  rw [he] at h
  exact h

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pointwise norm as an ordinary continuous real function. -/
def circleNormMap (f : C(AddCircle P, E)) : C(AddCircle P, ℝ) :=
  ⟨fun θ => ‖f θ‖, f.continuous.norm⟩

@[simp] theorem circleNormMap_apply (f : C(AddCircle P, E)) (θ : AddCircle P) :
    circleNormMap f θ = ‖f θ‖ := rfl

theorem circle_l2_norm_map (f : C(AddCircle P, E)) :
    (eLpNorm (circleNormMap f) 2 AddCircle.haarAddCircle).toReal =
      (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  exact congrArg ENNReal.toReal (eLpNorm_norm f f.continuous.aestronglyMeasurable)

/-- Pointwise domination implies domination of the genuine finite circle
`L²` norms, including between different target normed spaces. -/
theorem circle_l2_le_of_norm_le (f : C(AddCircle P, E)) (g : C(AddCircle P, F))
    (h : ∀ θ, ‖f θ‖ ≤ ‖g θ‖) :
    (eLpNorm f 2 AddCircle.haarAddCircle).toReal ≤
      (eLpNorm g 2 AddCircle.haarAddCircle).toReal :=
  ENNReal.toReal_mono (ContinuousMap.memLp (p := 2)
    (μ := AddCircle.haarAddCircle) ℝ g).ne
      (eLpNorm_mono f.continuous.aestronglyMeasurable h)

theorem circle_l2_sum_le {ι : Type*} [Fintype ι]
    (f : ι → C(AddCircle P, E)) :
    (eLpNorm (∑ i, f i) 2 AddCircle.haarAddCircle).toReal ≤
      ∑ i, (eLpNorm (f i) 2 AddCircle.haarAddCircle).toReal := by
  classical
  have hfin (i : ι) : eLpNorm (f i) 2 AddCircle.haarAddCircle ≠ ∞ :=
    (ContinuousMap.memLp (p := 2) (μ := AddCircle.haarAddCircle) ℝ (f i)).ne
  have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))
    (eLpNorm_sum_le (μ := AddCircle.haarAddCircle) (f := fun i => ⇑(f i))
      (s := Finset.univ) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  rw [ENNReal.toReal_sum (fun i _ => hfin i)] at h
  simpa only [ContinuousMap.coe_sum] using h

theorem circle_l2_const_smul (f : C(AddCircle P, E)) {M : ℝ} (hM : 0 ≤ M) :
    (eLpNorm (M • f) 2 AddCircle.haarAddCircle).toReal =
      M * (eLpNorm f 2 AddCircle.haarAddCircle).toReal := by
  rw [ContinuousMap.coe_smul, eLpNorm_const_smul, Real.enorm_of_nonneg hM,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

end ContinuousFlexibility.Analysis
