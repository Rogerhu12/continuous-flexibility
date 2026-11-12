import ContinuousFlexibility.Analysis.N06WeakAngularModes
import ContinuousFlexibility.Analysis.SpacesTorusWaves
import ContinuousFlexibility.Radial.R11bPhysicalCompleteness

/-!
# Fourier symbols of the actual canonical weak angular jets

Real and imaginary Fourier tests are obtained from the real parts of c times
a complex wave. The two choices c = 1 and c = -I identify the entire complex
coefficient. This proves the symbol at every weak order without requiring
smooth source representatives or a sectionwise weak-derivative hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

private instance n06WeakFourierSymbol_angle_finite : IsFiniteMeasure angleMeasure :=
  ⟨by
    rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top⟩

theorem n06_circleFourierWave_iteratedDeriv (n : ℤ) (j : ℕ) :
    iteratedDeriv j (circleFourierWave n) =
      fun θ => (2 * Complex.I * (n : ℂ)) ^ j * circleFourierWave n θ := by
  induction j with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    rw [deriv_const_mul_field, (circleFourierWave_hasDerivAt n θ).deriv, pow_succ]
    ring

theorem n06_realFourierWave_iteratedDeriv (c : ℂ) (n : ℤ) (j : ℕ) :
    iteratedDeriv j (fun θ => (c * circleFourierWave n θ).re) =
      fun θ => (c * (2 * Complex.I * (n : ℂ)) ^ j * circleFourierWave n θ).re := by
  funext θ
  have h := spaces_iteratedDeriv_clm Complex.reCLM
    ((contDiff_const (c := c)).mul (circleFourierWave_contDiff n)) j θ
  simpa only [Complex.reCLM_apply, iteratedDeriv_const_mul_field,
    n06_circleFourierWave_iteratedDeriv, mul_assoc] using h

theorem n06_memLp_circleFourierWave (n : ℤ) :
    MemLp (circleFourierWave n) 2 angleMeasure :=
  MemLp.of_bound (circleFourierWave_contDiff n).continuous.aestronglyMeasurable 1
    (Eventually.of_forall (fun θ => (circleFourierWave_norm n θ).le))

/-- Taking a real Fourier test commutes with the actual complex integral. -/
theorem n06_angular_realFourierWave_pairing {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (c : ℂ) (n : ℤ) :
    (∫ θ, f θ * (c * circleFourierWave n θ).re ∂angleMeasure) =
      (c * (∫ θ, circleFourierWave n θ * (f θ : ℂ) ∂angleMeasure)).re := by
  have hi : Integrable (fun θ => circleFourierWave n θ * (f θ : ℂ)) angleMeasure :=
    (n06_memLp_circleFourierWave n).integrable_mul hf.ofReal
  calc
    _ = ∫ θ, (c * (circleFourierWave n θ * (f θ : ℂ))).re ∂angleMeasure := by
      apply integral_congr_ae
      filter_upwards with θ
      simp only [← mul_assoc, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      ring
    _ = _ := by
      have h := integral_re (hi.const_mul c)
      change (∫ θ, (c * (circleFourierWave n θ * (f θ : ℂ))).re ∂angleMeasure) =
        (∫ θ, c * (circleFourierWave n θ * (f θ : ℂ)) ∂angleMeasure).re at h
      rw [integral_const_mul] at h
      exact h

theorem n06_canonicalL2_angular_sections
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) :
    ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      MemLp (fun θ => f (r, θ)) 2 angleMeasure := by
  have hf : MemLp (f : PolarPoint → ℝ) 2
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure) :=
    (congrArg (fun μ : Measure PolarPoint => MemLp (f : PolarPoint → ℝ) 2 μ)
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mp (Lp.memLp f)
  exact r11b_memLp_product_sections hf

/-- The Fourier symbol of a canonical weak derivative is the prescribed
power of 2 I n on almost every actual radial slice, including n = 0. -/
theorem WeakCanonicalAngularDerivative.n06_fourierCoeff_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j) (n : ℤ) :
    (fun r => circleFourierCoeff (fun θ => g (r, θ)) n)
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))]
        (fun r => (2 * Complex.I * (n : ℂ)) ^ j *
          circleFourierCoeff (fun θ => f (r, θ)) n) := by
  let w := circleFourierWave (-n)
  let z : ℂ := (2 * Complex.I * ((-n : ℤ) : ℂ)) ^ j
  let σ : ℝ := (-1) ^ j
  let If (r : ℝ) : ℂ := ∫ θ, w θ * (f (r, θ) : ℂ) ∂angleMeasure
  let Ig (r : ℝ) : ℂ := ∫ θ, w θ * (g (r, θ) : ℂ) ∂angleMeasure
  have hre (c : ℂ) :
      ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
        (c * Ig r).re = σ * (c * z * If r).re := by
    have he : ContDiff ℝ ∞ (fun θ => (c * w θ).re) :=
      Complex.reCLM.contDiff.comp ((contDiff_const (c := c)).mul
        (circleFourierWave_contDiff (-n)))
    have hp : Function.Periodic (fun θ => (c * w θ).re) Real.pi := by
      intro θ
      exact congrArg (fun x : ℂ => (c * x).re) (circleFourierWave_periodic (-n) θ)
    have hco := hfg.n06_coefficient_ae he hp
    filter_upwards [hco, n06_canonicalL2_angular_sections f,
      n06_canonicalL2_angular_sections g] with r hr hfr hgr
    have hd : iteratedDeriv j (fun θ => (c * w θ).re) =
        fun θ => (c * z * w θ).re := n06_realFourierWave_iteratedDeriv c (-n) j
    rw [hd] at hr
    change (∫ θ, g (r, θ) * (c * w θ).re ∂angleMeasure) =
      σ * (∫ θ, f (r, θ) * (c * z * w θ).re ∂angleMeasure) at hr
    rw [n06_angular_realFourierWave_pairing hgr c (-n),
      n06_angular_realFourierWave_pairing hfr (c * z) (-n)] at hr
    exact hr
  filter_upwards [hre 1, hre (-Complex.I)] with r hr hi
  have hcomplex : Ig r = (σ : ℂ) * (z * If r) := by
    apply Complex.ext
    · simpa only [one_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using hr
    · simpa only [mul_assoc, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hi
  have hsign : (σ : ℂ) * z = (2 * Complex.I * (n : ℂ)) ^ j := by
    simp only [σ, z, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, Int.cast_neg]
    rw [← mul_pow]
    congr 1
    ring
  rw [circleFourierCoeff_integral, circleFourierCoeff_integral]
  change (Real.pi : ℂ)⁻¹ * Ig r =
    (2 * Complex.I * (n : ℂ)) ^ j * ((Real.pi : ℂ)⁻¹ * If r)
  rw [hcomplex]
  calc
    _ = ((σ : ℂ) * z) * ((Real.pi : ℂ)⁻¹ * If r) := by ring
    _ = _ := by rw [hsign]

/-- Countably many frequencies and the whole finite jet row share one
radial full-measure set. This is the same-row compatibility needed for
finite Fourier truncations of the original zeroth field. -/
theorem n06_canonical_fourier_jets_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    (v : Fin (b + 1) → CanonicalL2 S K m)
    (hv : ∀ k, WeakCanonicalAngularDerivative S K m (v 0) (v k) k.val) :
    ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      ∀ k : Fin (b + 1), ∀ n : ℤ,
        circleFourierCoeff (fun θ => v k (r, θ)) n =
          (2 * Complex.I * (n : ℂ)) ^ k.val *
            circleFourierCoeff (fun θ => v 0 (r, θ)) n := by
  apply ae_all_iff.mpr
  intro k
  exact ae_all_iff.mpr (fun n => (hv k).n06_fourierCoeff_ae n)

end ContinuousFlexibility.Statements
