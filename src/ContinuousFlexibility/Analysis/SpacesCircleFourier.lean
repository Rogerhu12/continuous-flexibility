import ContinuousFlexibility.Analysis.CircleJetEncoding
import ContinuousFlexibility.Analysis.SpacesCircleCylinder
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier coefficients for the actual angular measure

The normalization is the one used by the prescribed circle norm: the
angular interval has length `π`, and the Fourier modes have frequency `2 n`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace ComplexConjugate ContDiff

private instance circleFourier_period_pos : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The complex Fourier mode on the angular circle of period `π`. -/
def circleFourierWave (n : ℤ) (θ : ℝ) : ℂ :=
  fourier n (θ : AddCircle Real.pi)

/-- Fourier coefficients with the actual angular interval and its normalized
Fourier convention. The underlying `angleMeasure` itself has mass `π`. -/
def circleFourierCoeff (f : ℝ → ℝ) (n : ℤ) : ℂ :=
  fourierCoeffOn Real.pi_pos (fun θ => (f θ : ℂ)) n

theorem circleFourierCoeff_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[angleMeasure] g) :
    circleFourierCoeff f = circleFourierCoeff g :=
  fourierCoeffOn_congr_ae Real.pi_pos (h.fun_comp fun x : ℝ => (x : ℂ))

theorem angleL2_integral_sq (f : AngleL2) :
    (∫ θ, (f θ) ^ 2 ∂angleMeasure) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    change (f θ) ^ 2 = inner ℝ (f θ) (f θ)
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Parseval with the exact, unnormalized `angleMeasure` convention. -/
theorem circleFourierCoeff_hasSum_sq (f : AngleL2) :
    HasSum (fun n : ℤ => ‖circleFourierCoeff f n‖ ^ 2) (Real.pi⁻¹ * ‖f‖ ^ 2) := by
  have hf : MemLp (fun θ : ℝ => (f θ : ℂ)) 2 angleMeasure := (Lp.memLp f).ofReal
  have hI : (∫ θ in (0 : ℝ)..Real.pi, ‖(f θ : ℂ)‖ ^ 2) = ‖f‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    change (∫ θ, ‖(f θ : ℂ)‖ ^ 2 ∂angleMeasure) = ‖f‖ ^ 2
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using angleL2_integral_sq f
  simpa only [circleFourierCoeff, sub_zero, smul_eq_mul, hI] using
    hasSum_sq_fourierCoeffOn Real.pi_pos hf

theorem circleFourierCoeff_integral (f : ℝ → ℝ) (n : ℤ) :
    circleFourierCoeff f n = (Real.pi : ℂ)⁻¹ *
      ∫ θ, circleFourierWave (-n) θ * (f θ : ℂ) ∂angleMeasure := by
  rw [circleFourierCoeff, fourierCoeffOn_eq_integral]
  simp only [sub_zero, intervalIntegral.integral_of_le Real.pi_pos.le, one_div,
    Complex.real_smul, Complex.ofReal_inv, smul_eq_mul, circleFourierWave, angleMeasure,
    fourier_coe_apply]

/-- Real input has conjugate-symmetric Fourier coefficients. -/
theorem circleFourierCoeff_neg (f : ℝ → ℝ) (n : ℤ) :
    circleFourierCoeff f (-n) = conj (circleFourierCoeff f n) := by
  rw [circleFourierCoeff_integral, circleFourierCoeff_integral, map_mul,
    map_inv₀, Complex.conj_ofReal, ← integral_conj]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    simp only [circleFourierWave, neg_neg, map_mul, Complex.conj_ofReal,
      fourier_neg, starRingEnd_self_apply]

end ContinuousFlexibility.Statements
