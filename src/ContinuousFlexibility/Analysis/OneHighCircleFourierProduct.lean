import ContinuousFlexibility.Analysis.OneHighCircleFourierBasic
import Mathlib.Analysis.LConvolution
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Multiplication and actual circle Fourier convolution

Absolute summability of one factor gives its uniformly convergent Fourier
series. Applying the continuous Fourier-coefficient functional to that series
after multiplication proves the full, infinite convolution formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal MeasureTheory

variable {P : ℝ} [Fact (0 < P)]

private theorem circleContinuous_integrable (f : C(AddCircle P, ℂ)) :
    Integrable (f : AddCircle P → ℂ) AddCircle.haarAddCircle :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (p := 1) (μ := AddCircle.haarAddCircle) ℂ f)

/-- Taking an actual Fourier coefficient is a continuous linear functional
on the space of continuous circle functions with its supremum norm. -/
def circleFourierCoeffCLM (n : ℤ) : C(AddCircle P, ℂ) →L[ℂ] ℂ where
  toFun f := fourierCoeff f n
  map_add' f g := by
    simpa only [ContinuousMap.coe_add, Pi.add_apply] using
      congrFun (fourierCoeff.add (circleContinuous_integrable f)
        (circleContinuous_integrable g)) n
  map_smul' c f := by
    simpa only [ContinuousMap.coe_smul, RingHom.id_apply] using
      fourierCoeff.const_smul (f : AddCircle P → ℂ) c n
  cont := by
    have h := (lp.lipschitzWith_one_eval (E := fun _ : ℤ => ℂ) 2 n).continuous.comp
      ((fourierBasis (T := P)).repr.continuous.comp
        (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ).continuous)
    simpa only [Function.comp_def, fourierBasis_repr, fourierCoeff_toLp] using h

@[simp] theorem circleFourierCoeffCLM_apply (n : ℤ) (f : C(AddCircle P, ℂ)) :
    circleFourierCoeffCLM n f = fourierCoeff f n := rfl

/-- Multiplication by a Fourier character shifts the coefficient index. -/
theorem circle_fourierCoeff_fourier_mul (g : C(AddCircle P, ℂ)) (k n : ℤ) :
    fourierCoeff ((fourier k : C(AddCircle P, ℂ)) * g) n = fourierCoeff g (n - k) := by
  rw [fourierCoeff_eq_intervalIntegral ((fourier k : C(AddCircle P, ℂ)) * g) n 0,
    fourierCoeff_eq_intervalIntegral g (n - k) 0]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [ContinuousMap.mul_apply, smul_eq_mul]
  rw [← mul_assoc, ← fourier_add, show -n + k = -(n - k) by omega]

/-- The convolution series for a product converges to its actual Fourier
coefficient; there is no finite-support hypothesis. -/
theorem circle_fourierCoeff_hasSum_mul (f g : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count) (n : ℤ) :
    HasSum (fun k : ℤ => fourierCoeff f k * fourierCoeff g (n - k))
      (fourierCoeff (f * g) n) := by
  have hs : Summable (fun k : ℤ => ‖fourierCoeff f k‖) :=
    integrable_count_iff.mp (memLp_one_iff_integrable.mp hf)
  have h := (circleFourierCoeffCLM n).hasSum
    ((hasSum_fourier_series_of_summable hs.of_norm).mul_right g)
  simpa only [smul_mul_assoc, map_smul, circleFourierCoeffCLM_apply,
    circle_fourierCoeff_fourier_mul, smul_eq_mul] using h

/-- Pointwise multiplication corresponds to the complete integer
convolution of the two actual Fourier coefficient sequences. -/
theorem circle_fourierCoeff_mul_eq_tsum (f g : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count) (n : ℤ) :
    fourierCoeff (f * g) n =
      ∑' k : ℤ, fourierCoeff f k * fourierCoeff g (n - k) :=
  (circle_fourierCoeff_hasSum_mul f g hf n).tsum_eq.symm

/-- The extended norm of a product coefficient is dominated by the
positive convolution used in the general one-high-factor estimates. -/
theorem circle_enorm_fourierCoeff_mul_le_lconvolution (f g : C(AddCircle P, ℂ))
    (hf : MemLp (fourierCoeff f) 1 Measure.count) (n : ℤ) :
    ‖fourierCoeff (f * g) n‖ₑ ≤
      ((fun k : ℤ => ‖fourierCoeff f k‖ₑ) ⋆ₗ[Measure.count]
        (fun k : ℤ => ‖fourierCoeff g k‖ₑ)) n := by
  rw [circle_fourierCoeff_mul_eq_tsum f g hf n, lconvolution_def, lintegral_count]
  simpa only [enorm_mul, sub_eq_add_neg, add_comm] using
    (enorm_tsum_le_tsum_enorm
      (f := fun k : ℤ => fourierCoeff f k * fourierCoeff g (n - k)))

end ContinuousFlexibility.Analysis
