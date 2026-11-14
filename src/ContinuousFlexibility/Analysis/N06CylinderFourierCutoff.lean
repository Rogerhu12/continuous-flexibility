module

public import ContinuousFlexibility.Analysis.N06WeakFourierSymbol
public import ContinuousFlexibility.Analysis.N06FourierCutoff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite Fourier cutoffs on an actual product L² cylinder

The coefficients are the original half-period integrals. Their real and
imaginary parts belong to radial L², so every finite angular derivative of
a cutoff is jointly L². Radial dominated convergence then proves strong
convergence in the original product measure, with no smooth source assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n06_circleFourierCoeff_parts {f : ℝ → ℝ}
    (hf : MemLp f 2 angleMeasure) (n : ℤ) :
    (circleFourierCoeff f n).re = Real.pi⁻¹ *
        (∫ θ, f θ * (circleFourierWave (-n) θ).re ∂angleMeasure) ∧
      (circleFourierCoeff f n).im = Real.pi⁻¹ *
        (∫ θ, f θ * (circleFourierWave (-n) θ).im ∂angleMeasure) := by
  have hr := n06_angular_realFourierWave_pairing hf 1 (-n)
  have hi := n06_angular_realFourierWave_pairing hf (-Complex.I) (-n)
  simp only [one_mul] at hr
  simp only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at hi
  constructor
  · rw [circleFourierCoeff_integral, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hr]
  · rw [circleFourierCoeff_integral, ← Complex.ofReal_inv]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← hi]

variable {μ : Measure ℝ} [SFinite μ]

/-- Both components of an actual complex Fourier coefficient lie in radial L². -/
theorem n06_radial_fourierCoeff_memLp {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) (n : ℤ) :
    MemLp (fun r => (circleFourierCoeff (fun θ => f (r, θ)) n).re) 2 μ ∧
      MemLp (fun r => (circleFourierCoeff (fun θ => f (r, θ)) n).im) 2 μ := by
  have hRe : MemLp (fun θ => (circleFourierWave (-n) θ).re) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous
      (Complex.continuous_re.comp (circleFourierWave_contDiff (-n)).continuous)
  have hIm : MemLp (fun θ => (circleFourierWave (-n) θ).im) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous
      (Complex.continuous_im.comp (circleFourierWave_contDiff (-n)).continuous)
  have hr := (r11b_memLp_modeCoefficient hf hRe).1.const_mul Real.pi⁻¹
  have hi := (r11b_memLp_modeCoefficient hf hIm).1.const_mul Real.pi⁻¹
  have hre : (fun r => (circleFourierCoeff (fun θ => f (r, θ)) n).re) =ᵐ[μ]
      (fun r => Real.pi⁻¹ * ∫ θ, f (r, θ) * (circleFourierWave (-n) θ).re ∂angleMeasure) :=
    (r11b_memLp_product_sections hf).mono (fun _ h => (n06_circleFourierCoeff_parts h n).1)
  have him : (fun r => (circleFourierCoeff (fun θ => f (r, θ)) n).im) =ᵐ[μ]
      (fun r => Real.pi⁻¹ * ∫ θ, f (r, θ) * (circleFourierWave (-n) θ).im ∂angleMeasure) :=
    (r11b_memLp_product_sections hf).mono (fun _ h => (n06_circleFourierCoeff_parts h n).2)
  exact ⟨(memLp_congr_ae hre).mpr hr, (memLp_congr_ae him).mpr hi⟩

theorem n06_product_fourierTerm_memLp {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) (n : ℤ)
    {e : ℝ → ℂ} (he : Continuous e) :
    MemLp (fun p : PolarPoint =>
      (circleFourierCoeff (fun θ => f (p.1, θ)) n * e p.2).re) 2
        (μ.prod angleMeasure) := by
  have heR : MemLp (fun θ => (e θ).re) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous (Complex.continuous_re.comp he)
  have heI : MemLp (fun θ => (e θ).im) 2 angleMeasure :=
    memLp_angleMeasure_of_continuous (Complex.continuous_im.comp he)
  have hr : MemLp (fun p : PolarPoint =>
      (circleFourierCoeff (fun θ => f (p.1, θ)) n).re * (e p.2).re) 2
        (μ.prod angleMeasure) :=
    r11b_memLp_tensor (n06_radial_fourierCoeff_memLp hf n).1 heR
  have hi : MemLp (fun p : PolarPoint =>
      (circleFourierCoeff (fun θ => f (p.1, θ)) n).im * (e p.2).im) 2
        (μ.prod angleMeasure) :=
    r11b_memLp_tensor (n06_radial_fourierCoeff_memLp hf n).2 heI
  have hsub : MemLp (fun p : PolarPoint =>
      (circleFourierCoeff (fun θ => f (p.1, θ)) n).re * (e p.2).re -
        (circleFourierCoeff (fun θ => f (p.1, θ)) n).im * (e p.2).im) 2
          (μ.prod angleMeasure) := hr.sub hi
  simpa only [Complex.mul_re] using hsub

/-- A finite angular polynomial of the original cylinder representative. -/
def n06CylinderFourierCut (s : Finset ℤ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  n06CircleFourierCut s (fun θ => f (p.1, θ)) p.2

/-- Pure angular derivatives of a finite cutoff are actual derivatives of
the same polynomial; only its angular waves are differentiated. -/
theorem n06CylinderFourierCut_angularJet (s : Finset ℤ) (f : PolarPoint → ℝ) (j : ℕ) :
    mixedDerivative 0 j (n06CylinderFourierCut s f) =
      fun p => ∑ n ∈ s, (circleFourierCoeff (fun θ => f (p.1, θ)) n *
        ((2 * Complex.I * (n : ℂ)) ^ j * circleFourierWave n p.2)).re := by
  funext p
  have hsmooth (n : ℤ) : ContDiff ℝ ∞
      (fun θ => (circleFourierCoeff (fun η => f (p.1, η)) n *
        circleFourierWave n θ).re) :=
    Complex.reCLM.contDiff.comp
      ((contDiff_const (c := circleFourierCoeff (fun η => f (p.1, η)) n)).mul
        (circleFourierWave_contDiff n))
  simp only [mixedDerivative, iteratedDeriv_zero, n06CylinderFourierCut,
    n06CircleFourierCut, circleFourierPolynomial, Complex.re_sum]
  rw [iteratedDeriv_fun_sum (I := s) (n := j) (x := p.2)
    (f := fun n θ => (circleFourierCoeff (fun η => f (p.1, η)) n *
      circleFourierWave n θ).re)
    (fun n _ => (hsmooth n).contDiffAt.of_le (by simp))]
  apply Finset.sum_congr rfl
  intro n _
  rw [n06_realFourierWave_iteratedDeriv]
  simp only [mul_assoc]

theorem n06CylinderFourierCut_angularJet_memLp {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) (s : Finset ℤ) (j : ℕ) :
    MemLp (mixedDerivative 0 j (n06CylinderFourierCut s f)) 2 (μ.prod angleMeasure) := by
  rw [n06CylinderFourierCut_angularJet]
  apply memLp_finsetSum s (f := fun (n : ℤ) (p : PolarPoint) =>
    (circleFourierCoeff (fun θ => f (p.1, θ)) n *
      ((2 * Complex.I * (n : ℂ)) ^ j * circleFourierWave n p.2)).re)
  intro n _
  exact n06_product_fourierTerm_memLp hf n
    (e := fun θ => (2 * Complex.I * (n : ℂ)) ^ j * circleFourierWave n θ)
    (continuous_const.mul (circleFourierWave_contDiff n).continuous)

theorem n06CylinderFourierCut_memLp {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) (s : Finset ℤ) :
    MemLp (n06CylinderFourierCut s f) 2 (μ.prod angleMeasure) := by
  simpa only [spaces_mixedDerivative_zero] using
    n06CylinderFourierCut_angularJet_memLp hf s 0

/-- Actual squared projection errors converge under radial integration.
The majorant is four times the original fiber square integral. -/
theorem n06CylinderFourierCut_error_tendsto {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) :
    Tendsto (fun N => ∫ p,
      (n06CylinderFourierCut (n06FourierCutoff N) f p - f p) ^ 2
        ∂μ.prod angleMeasure) atTop (𝓝 0) := by
  let E : ℝ → ℝ := fun r => 4 * ∫ θ, f (r, θ) ^ 2 ∂angleMeasure
  let e (N : ℕ) (r : ℝ) : ℝ := ∫ θ,
    (n06CircleFourierCut (n06FourierCutoff N) (fun θ => f (r, θ)) θ - f (r, θ)) ^ 2
      ∂angleMeasure
  have hP (N : ℕ) : MemLp (n06CylinderFourierCut (n06FourierCutoff N) f) 2
      (μ.prod angleMeasure) := n06CylinderFourierCut_memLp hf _
  have hE : Integrable E μ := hf.integrable_sq.integral_prod_left.const_mul 4
  have heI (N : ℕ) : Integrable (e N) μ := by
    simpa only [e, n06CylinderFourierCut, Pi.sub_apply] using
      ((hP N).sub hf).integrable_sq.integral_prod_left
  have hbound (N : ℕ) : ∀ᵐ r ∂μ, ‖e N r‖ ≤ E r := by
    filter_upwards [r11b_memLp_product_sections hf] with r hr
    have hnonneg : 0 ≤ e N r := integral_nonneg (fun _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    exact n06CircleFourierCut_error_sq_le hr _ (n06FourierCutoff_neg N)
  have hlimit : ∀ᵐ r ∂μ, Tendsto (fun N => e N r) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [r11b_memLp_product_sections hf] with r hr
    exact n06CircleFourierCut_error_tendsto hr
  have ht := tendsto_integral_of_dominated_convergence E
    (fun N => (heI N).aestronglyMeasurable) hE hbound hlimit
  have ht' : Tendsto (fun N => ∫ r, e N r ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using ht
  have heq (N : ℕ) :
      (∫ p, (n06CylinderFourierCut (n06FourierCutoff N) f p - f p) ^ 2
        ∂μ.prod angleMeasure) = ∫ r, e N r ∂μ :=
    integral_prod _ ((hP N).sub hf).integrable_sq
  exact ht'.congr' (Eventually.of_forall (fun N => (heq N).symm))

theorem n06CylinderFourierCut_tendsto {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod angleMeasure)) :
    Tendsto (fun N => (n06CylinderFourierCut_memLp hf (n06FourierCutoff N)).toLp
      (n06CylinderFourierCut (n06FourierCutoff N) f)) atTop (𝓝 (hf.toLp f)) :=
  (r11b_tendsto_toLp_iff_integral_sq_sub
    (fun N => n06CylinderFourierCut_memLp hf (n06FourierCutoff N)) hf).mpr
      (n06CylinderFourierCut_error_tendsto hf)

end ContinuousFlexibility.Statements
