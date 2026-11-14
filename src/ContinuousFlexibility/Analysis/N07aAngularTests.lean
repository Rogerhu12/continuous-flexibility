module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets
public import ContinuousFlexibility.Analysis.SpacesTorusWaves

/-!
# Actual Fourier tests for the canonical weak angular derivative

Compactly supported smooth radial functions times the genuine period-`π`
Fourier waves are admissible canonical tests. The defining weak equation
therefore gives the Fourier multiplier `(2 I n)^j`, without imposing any
radial regularity on the source or its weak derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07aCanonicalMeasure_finite (m : ℕ) : IsFiniteMeasure (canonicalMeasure S K m) := by
  constructor
  rw [canonicalMeasure, Measure.restrict_apply_univ, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Continuity on the closed rectangle gives the required actual `L²` class. -/
theorem n07aCanonicalContinuous_memLp (m : ℕ) {f : PolarPoint → ℂ}
    (hf : Continuous f) : MemLp f 2 (canonicalMeasure S K m) := by
  let := n07aCanonicalMeasure_finite (S := S) (K := K) m
  let Q : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc 0 Real.pi
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hQ.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable M
  have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  exact hM ⟨p, ⟨Ioo_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩, rfl⟩

theorem n07aAngularWave_iteratedDeriv (n : ℤ) (j : ℕ) :
    iteratedDeriv j (circleFourierWave n) =
      fun θ => (2 * Complex.I * (n : ℂ)) ^ j * circleFourierWave n θ := by
  induction j with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    rw [deriv_const_mul_field, (circleFourierWave_hasDerivAt n θ).deriv, pow_succ]
    ring

/-- A separated complex test; real parts will supply the real weak equation. -/
def n07aAngularWave (η : ℝ → ℂ) (n : ℤ) (p : PolarPoint) : ℂ :=
  η p.1 * circleFourierWave n p.2

def n07aAngularWaveTest (η : ℝ → ℂ) (c : ℂ) (n : ℤ) (p : PolarPoint) : ℝ :=
  (c * n07aAngularWave η n p).re

theorem n07aAngularWave_contDiff {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) (n : ℤ) :
    ContDiff ℝ ∞ (n07aAngularWave η n) :=
  (hη.comp contDiff_fst).mul
    ((circleFourierWave_contDiff n).comp contDiff_snd)

theorem n07aAngularWaveTest_contDiff {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η)
    (c : ℂ) (n : ℤ) : ContDiff ℝ ∞ (n07aAngularWaveTest η c n) :=
  Complex.reCLM.contDiff.comp (contDiff_const.mul (n07aAngularWave_contDiff hη n))

theorem n07aAngularWaveTest_periodic (η : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    Function.Periodic (n07aAngularWaveTest η c n) (0, Real.pi) := by
  intro p
  simp only [n07aAngularWaveTest, n07aAngularWave, Prod.fst_add, Prod.snd_add,
    add_zero, circleFourierWave_periodic n p.2]

/-- The compact radial support is exactly the support allowed by the frozen test class. -/
theorem n07aAngularWaveTest_canonical (m : ℕ) {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo (K.left m) (K.right m))
    (hzero : ∀ r, r ∉ J → η r = 0) (c : ℂ) (n : ℤ) :
    CanonicalTest S K m (n07aAngularWaveTest η c n) := by
  refine ⟨n07aAngularWaveTest_contDiff hη c n,
    n07aAngularWaveTest_periodic η c n, J, hJ, hJI, ?_⟩
  intro r hr θ
  simp only [n07aAngularWaveTest, n07aAngularWave, hzero r hr,
    zero_mul, mul_zero, Complex.zero_re]

theorem n07aAngularWaveTest_mixedDerivative {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η)
    (c : ℂ) (n : ℤ) (j : ℕ) (p : PolarPoint) :
    mixedDerivative 0 j (n07aAngularWaveTest η c n) p =
      n07aAngularWaveTest η (c * (2 * Complex.I * (n : ℂ)) ^ j) n p := by
  have he : n07aAngularWaveTest η c n =
      fun q : PolarPoint => (c * η q.1 * circleFourierWave n q.2).re := by
    funext q
    simp only [n07aAngularWaveTest, n07aAngularWave, mul_assoc]
  rw [he, spaces_mixedDerivative_real_product hη (circleFourierWave_contDiff n) c 0 j p,
    iteratedDeriv_zero, n07aAngularWave_iteratedDeriv]
  unfold n07aAngularWaveTest n07aAngularWave
  congr 1
  ring

theorem n07aAngularWave_integrable_mul (m : ℕ) {η : ℝ → ℂ}
    (hη : ContDiff ℝ ∞ η) (n : ℤ) (f : CanonicalL2 S K m) :
    Integrable (fun p => n07aAngularWave η n p * (f p : ℂ)) (canonicalMeasure S K m) := by
  have hw := n07aCanonicalContinuous_memLp (S := S) (K := K) m
    (n07aAngularWave_contDiff hη n).continuous
  exact memLp_one_iff_integrable.mp (hw.mul (Lp.memLp f).ofReal)

private theorem n07aAngularWaveTest_integral (m : ℕ) {η : ℝ → ℂ}
    (hη : ContDiff ℝ ∞ η) (c : ℂ) (n : ℤ) (f : CanonicalL2 S K m) :
    (∫ p, f p * n07aAngularWaveTest η c n p ∂canonicalMeasure S K m) =
      (c * ∫ p, n07aAngularWave η n p * (f p : ℂ) ∂canonicalMeasure S K m).re := by
  have hi := (n07aAngularWave_integrable_mul m hη n f).const_mul c
  have hr := integral_re hi
  change (∫ p, (c * (n07aAngularWave η n p * (f p : ℂ))).re
      ∂canonicalMeasure S K m) =
    (∫ p, c * (n07aAngularWave η n p * (f p : ℂ)) ∂canonicalMeasure S K m).re at hr
  rw [integral_const_mul] at hr
  simpa only [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, n07aAngularWaveTest, mul_comm] using hr

/-- The defining real weak equation determines the complex Fourier symbol after
testing with both real and imaginary parts of the actual wave. -/
theorem n07aAngularWeak_wave_pairing (m : ℕ) {f g : CanonicalL2 S K m} {j : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) {J : Set ℝ}
    (hJ : IsCompact J) (hJI : J ⊆ Ioo (K.left m) (K.right m))
    (hzero : ∀ r, r ∉ J → η r = 0) (n : ℤ) :
    (∫ p, n07aAngularWave η n p * (g p : ℂ) ∂canonicalMeasure S K m) =
      (-1 : ℂ) ^ j * (2 * Complex.I * (n : ℂ)) ^ j *
        ∫ p, n07aAngularWave η n p * (f p : ℂ) ∂canonicalMeasure S K m := by
  have hre (c : ℂ) :
      (c * ∫ p, n07aAngularWave η n p * (g p : ℂ) ∂canonicalMeasure S K m).re =
        (-1 : ℝ) ^ j *
          (c * ((2 * Complex.I * (n : ℂ)) ^ j *
            ∫ p, n07aAngularWave η n p * (f p : ℂ) ∂canonicalMeasure S K m)).re := by
    have h := hfg (n07aAngularWaveTest η c n)
      (n07aAngularWaveTest_canonical m hη hJ hJI hzero c n)
    simp_rw [n07aAngularWaveTest_mixedDerivative hη] at h
    rw [n07aAngularWaveTest_integral m hη, n07aAngularWaveTest_integral m hη] at h
    simpa only [mul_assoc] using h
  have hcomplex :
      (∫ p, n07aAngularWave η n p * (g p : ℂ) ∂canonicalMeasure S K m) =
        Complex.ofReal ((-1 : ℝ) ^ j) * ((2 * Complex.I * (n : ℂ)) ^ j *
          ∫ p, n07aAngularWave η n p * (f p : ℂ) ∂canonicalMeasure S K m) := by
    apply Complex.ext
    · simpa only [one_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hre 1
    · simpa only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        using hre (-Complex.I)
  simpa only [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, mul_assoc]
    using hcomplex

/-- With the Fourier coefficient convention `wave (-n)`, weak angular
differentiation has exactly the positive symbol `(2 I n)^j`. -/
theorem n07aAngularWeak_fourier_pairing (m : ℕ) {f g : CanonicalL2 S K m} {j : ℕ}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η) {J : Set ℝ}
    (hJ : IsCompact J) (hJI : J ⊆ Ioo (K.left m) (K.right m))
    (hzero : ∀ r, r ∉ J → η r = 0) (n : ℤ) :
    (∫ p, n07aAngularWave η (-n) p * (g p : ℂ) ∂canonicalMeasure S K m) =
      (2 * Complex.I * (n : ℂ)) ^ j *
        ∫ p, n07aAngularWave η (-n) p * (f p : ℂ) ∂canonicalMeasure S K m := by
  have h := n07aAngularWeak_wave_pairing m hfg hη hJ hJI hzero (-n)
  have hs : (-1 : ℂ) ^ j * (2 * Complex.I * ((-n : ℤ) : ℂ)) ^ j =
      (2 * Complex.I * (n : ℂ)) ^ j := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  rwa [hs] at h

end ContinuousFlexibility.Statements
