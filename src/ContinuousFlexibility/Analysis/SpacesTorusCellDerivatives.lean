import ContinuousFlexibility.Analysis.SpacesTorusCell
import ContinuousFlexibility.Analysis.SpacesTorusWaves

/-!
# Fourier coefficients of localized physical mixed jets

The coefficient identities use integration by parts on the actual material
cylinder. Compact radial localization removes the radial boundary, while
the angular period removes the other boundary. The cell chart preserves
the normalized measure, including its exact factor `1 / (6π)`.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology ComplexConjugate

set_option backward.isDefEq.respectTransparency false

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem spacesPhysicalFourierWave_periodic (n : ℤ) (j : SpacesTorusFrequency) :
    Function.Periodic (spacesPhysicalFourierWave n j) (0, Real.pi) := by
  rintro ⟨x, θ⟩
  simp only [spacesPhysicalFourierWave, Prod.mk_add_mk, add_zero]
  congr 1
  unfold spacesUnitFourierAffine
  have he : 1 / Real.pi * (θ + Real.pi) + 0 =
      (1 / Real.pi * θ + 0) + 1 := by field_simp; ring
  rw [he, AddCircle.coe_add_period]

theorem spacesPhysicalFourierWave_integrable_mul (n : ℤ) (j : SpacesTorusFrequency)
    {v : PolarPoint → ℝ} (hv : IsCylinderTest v) :
    Integrable (fun p => spacesPhysicalFourierWave n j p * (v p : ℂ))
      materialCylinderMeasure := by
  apply hv.spaces_integrable.ofReal.bdd_mul
    (spacesPhysicalFourierWave_contDiff n j).continuous.aestronglyMeasurable
  exact Eventually.of_forall (fun p => (spacesPhysicalFourierWave_norm n j p).le)

/-- Complex integration by parts for one physical Fourier wave. -/
theorem spacesPhysicalFourierWave_integral_mixedDerivative
    (n : ℤ) (j : SpacesTorusFrequency) {v : PolarPoint → ℝ}
    (hv : IsCylinderTest v) (a b : ℕ) :
    (∫ p, spacesPhysicalFourierWave n j p * (mixedDerivative a b v p : ℂ)
      ∂materialCylinderMeasure) =
      (-1 : ℂ) ^ (a + b) *
        (spacesUnitFourierSymbol (j 0) (1 / 6) ^ a *
          spacesUnitFourierSymbol (j 1) (1 / Real.pi) ^ b) *
        (∫ p, spacesPhysicalFourierWave n j p * (v p : ℂ) ∂materialCylinderMeasure) := by
  let w := spacesPhysicalFourierWave n j
  let z := spacesUnitFourierSymbol (j 0) (1 / 6) ^ a *
    spacesUnitFourierSymbol (j 1) (1 / Real.pi) ^ b
  have hi := spacesPhysicalFourierWave_integrable_mul n j hv
  have hdi := spacesPhysicalFourierWave_integrable_mul n j (hv.mixedDerivative a b)
  have hre (c : ℂ) :
      (c * (z * (∫ p, w p * (v p : ℂ) ∂materialCylinderMeasure))).re =
        (-1 : ℝ) ^ (a + b) *
          (c * (∫ p, w p * (mixedDerivative a b v p : ℂ)
            ∂materialCylinderMeasure)).re := by
    have hf : ContDiff ℝ ∞ (fun p => (c * w p).re) :=
      Complex.reCLM.contDiff.comp ((contDiff_const (c := c)).mul
        (spacesPhysicalFourierWave_contDiff n j))
    have hp : Function.Periodic (fun p => (c * w p).re) (0, Real.pi) := by
      intro p
      dsimp only
      rw [show w (p + (0, Real.pi)) = w p from spacesPhysicalFourierWave_periodic n j p]
    have h := spaces_integral_mixedDerivative_mul hf hp hv a b
    have hd : mixedDerivative a b (fun p => (c * w p).re) =
        fun p => (c * z * w p).re := by
      funext p
      rw [spacesPhysicalFourierWave_mixedDerivative]
      dsimp only [z]
      congr 1
      ring
    rw [hd] at h
    have hi' : Integrable (fun p => c * z * (w p * (v p : ℂ))) materialCylinderMeasure :=
      hi.const_mul (c * z)
    have hdi' : Integrable (fun p => c * (w p * (mixedDerivative a b v p : ℂ)))
        materialCylinderMeasure := hdi.const_mul c
    have he : (∫ p, (c * z * w p).re * v p ∂materialCylinderMeasure) =
        (c * (z * (∫ p, w p * (v p : ℂ) ∂materialCylinderMeasure))).re := by
      have hr := integral_re hi'
      change (∫ p, (c * z * (w p * (v p : ℂ))).re ∂materialCylinderMeasure) =
        (∫ p, c * z * (w p * (v p : ℂ)) ∂materialCylinderMeasure).re at hr
      rw [integral_const_mul] at hr
      simpa only [← mul_assoc, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using hr
    have he' : (∫ p, (c * w p).re * mixedDerivative a b v p ∂materialCylinderMeasure) =
        (c * (∫ p, w p * (mixedDerivative a b v p : ℂ) ∂materialCylinderMeasure)).re := by
      have hr := integral_re hdi'
      change (∫ p, (c * (w p * (mixedDerivative a b v p : ℂ))).re ∂materialCylinderMeasure) =
        (∫ p, c * (w p * (mixedDerivative a b v p : ℂ)) ∂materialCylinderMeasure).re at hr
      rw [integral_const_mul] at hr
      simpa only [← mul_assoc, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero] using hr
    rw [he, he'] at h
    exact h
  have hcomplex : z * (∫ p, w p * (v p : ℂ) ∂materialCylinderMeasure) =
      Complex.ofReal ((-1 : ℝ) ^ (a + b)) *
        (∫ p, w p * (mixedDerivative a b v p : ℂ) ∂materialCylinderMeasure) := by
    apply Complex.ext
    · simpa only [one_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hre 1
    · simpa only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hre (-Complex.I)
  have hs : ((-1 : ℂ) ^ (a + b)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one] at hcomplex
  change _ = (-1 : ℂ) ^ (a + b) * z * _
  rw [mul_assoc, hcomplex, ← mul_assoc, ← pow_two, hs, one_mul]

end ContinuousFlexibility.Statements
