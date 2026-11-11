import ContinuousFlexibility.Analysis.OneHighCylinderDerivativeMultiplier
import ContinuousFlexibility.Analysis.OneHighCylinderFourierInverseKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Genuine coordinate derivatives of the mixed inverse integral

Differentiation under the full mixed integral is justified by an integrable
first frequency moment. The derivative bound is independent of the physical
point because every inverse Fourier character has norm one.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

theorem cylinderInverseCharacter_hasDerivAt_radial (ζ : ℝ × ℤ) (r : ℝ) (θ : AddCircle P) :
    HasDerivAt (fun x : ℝ => cylinderInverseCharacter (x, θ) ζ)
      (cylinderDerivativeMultiplier P 1 0 ζ * cylinderInverseCharacter (r, θ) ζ) r := by
  have hlin : HasDerivAt (fun x : ℝ => ζ.1 * x) ζ.1 r := by
    simpa only [mul_one] using (hasDerivAt_id r).const_mul ζ.1
  have hchar := (Real.hasDerivAt_fourierChar (ζ.1 * r)).scomp r hlin
  have hmul := hchar.mul_const (fourier ζ.2 θ)
  convert hmul using 1 <;>
    simp only [cylinderInverseCharacter, cylinderDerivativeMultiplier, pow_one, pow_zero,
      mul_one, Function.comp_def, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat] <;> ring

theorem cylinderInverseCharacter_hasDerivAt_angular (ζ : ℝ × ℤ) (r x : ℝ) :
    HasDerivAt (fun y : ℝ => cylinderInverseCharacter (r, (y : AddCircle P)) ζ)
      (cylinderDerivativeMultiplier P 0 1 ζ *
        cylinderInverseCharacter (r, (x : AddCircle P)) ζ) x := by
  have hmul := (hasDerivAt_fourier P ζ.2 x).const_mul
    (Real.fourierChar (ζ.1 * r) : ℂ)
  convert hmul using 1 <;>
    simp only [cylinderInverseCharacter, cylinderDerivativeMultiplier, pow_one, pow_zero,
      one_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_intCast] <;> ring

private theorem cylinderFourierInverse_hasDerivAt_of_character
    (p : ℝ → ℝ × AddCircle P) (M : ℝ × ℤ → ℂ)
    (hchar : ∀ ζ x, HasDerivAt (fun y : ℝ => cylinderInverseCharacter (p y) ζ)
      (M ζ * cylinderInverseCharacter (p x) ζ) x)
    {G : ℝ × ℤ → ℂ} (hG : Integrable G cylinderFrequencyMeasure)
    (hMG : Integrable (fun ζ => M ζ * G ζ) cylinderFrequencyMeasure) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cylinderFourierInverse G (p y))
      (cylinderFourierInverse (fun ζ => M ζ * G ζ) (p x)) x := by
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := cylinderFrequencyMeasure) (s := (univ : Set ℝ))
    (F := fun y ζ => cylinderInverseCharacter (p y) ζ * G ζ)
    (F' := fun y ζ => cylinderInverseCharacter (p y) ζ * (M ζ * G ζ))
    (bound := fun ζ => ‖M ζ * G ζ‖) (x₀ := x) (Filter.univ_mem)
    (Eventually.of_forall fun y => (integrable_cylinderInverseCharacter_mul hG (p y)).aestronglyMeasurable)
    (integrable_cylinderInverseCharacter_mul hG (p x))
    (integrable_cylinderInverseCharacter_mul hMG (p x)).aestronglyMeasurable
    (Eventually.of_forall fun ζ y _ => by
      simp only [norm_mul, norm_cylinderInverseCharacter, one_mul, le_refl])
    hMG.norm
    (Eventually.of_forall fun ζ y _ => by
      convert (hchar ζ y).mul_const (G ζ) using 1 <;> ring)
  exact hderiv.2

theorem cylinderFourierInverse_hasDerivAt_radial {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure)
    (hDG : Integrable (fun ζ => cylinderDerivativeMultiplier P 1 0 ζ * G ζ)
      cylinderFrequencyMeasure) (r : ℝ) (θ : AddCircle P) :
    HasDerivAt (fun x : ℝ => cylinderFourierInverse G (x, θ))
      (cylinderFourierInverse (fun ζ => cylinderDerivativeMultiplier P 1 0 ζ * G ζ) (r, θ)) r :=
  cylinderFourierInverse_hasDerivAt_of_character (fun x => (x, θ))
    (cylinderDerivativeMultiplier P 1 0)
    (fun ζ x => cylinderInverseCharacter_hasDerivAt_radial ζ x θ) hG hDG r

theorem cylinderFourierInverse_hasDerivAt_angular {G : ℝ × ℤ → ℂ}
    (hG : Integrable G cylinderFrequencyMeasure)
    (hDG : Integrable (fun ζ => cylinderDerivativeMultiplier P 0 1 ζ * G ζ)
      cylinderFrequencyMeasure) (r x : ℝ) :
    HasDerivAt (fun y : ℝ => cylinderFourierInverse G (r, (y : AddCircle P)))
      (cylinderFourierInverse (fun ζ => cylinderDerivativeMultiplier P 0 1 ζ * G ζ)
        (r, (x : AddCircle P))) x :=
  cylinderFourierInverse_hasDerivAt_of_character (fun y => (r, (y : AddCircle P)))
    (cylinderDerivativeMultiplier P 0 1)
    (fun ζ x => cylinderInverseCharacter_hasDerivAt_angular ζ r x) hG hDG x

end ContinuousFlexibility.Analysis
