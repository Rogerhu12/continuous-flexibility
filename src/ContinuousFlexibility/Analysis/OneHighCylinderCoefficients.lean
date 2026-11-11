import ContinuousFlexibility.Analysis.OneHighCircleFourierParseval
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Actual Fourier coefficients on the cylinder

The angular transform uses the genuine circle Fourier coefficients. Their
radial square integrability follows from Parseval and Fubini applied to the
original physical function. Thus the radial `L²` Fourier transform below is
defined on every continuous, square-integrable cylinder function, without an
extra radial `L¹` or compact-support assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Set
open scoped ENNReal FourierTransform

variable {P : ℝ} [Fact (0 < P)]

/-- Physical measure with normalized angular Haar measure. -/
def cylinderPhysicalMeasure (P : ℝ) [Fact (0 < P)] : Measure (ℝ × AddCircle P) :=
  volume.prod AddCircle.haarAddCircle

/-- The angular Fourier coefficient as a function of the radial variable. -/
def cylinderAngularCoefficient (f : ℝ × AddCircle P → ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  fourierCoeff (fun θ => f (r, θ)) n

@[simp] theorem cylinderAngularCoefficient_apply (f : ℝ × AddCircle P → ℂ)
    (n : ℤ) (r : ℝ) :
    cylinderAngularCoefficient f n r = fourierCoeff (fun θ => f (r, θ)) n := rfl

/-- Compact angular integration preserves radial continuity. -/
theorem continuous_cylinderAngularCoefficient {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) (n : ℤ) : Continuous (cylinderAngularCoefficient f n) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      fourier (-n) (p.2 : AddCircle P) • f (p.1, (p.2 : AddCircle P))) :=
    (((fourier (-n)).continuous.comp (AddCircle.continuous_mk' P)).comp continuous_snd).smul
      (hf.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' P).comp continuous_snd)))
  have hi : Continuous (fun r : ℝ => ∫ θ in Icc (0 : ℝ) P,
      fourier (-n) (θ : AddCircle P) • f (r, (θ : AddCircle P)) ∂volume) :=
    continuous_parametric_integral_of_continuous
      (μ := (volume : Measure ℝ)) (f := fun (r : ℝ) (θ : ℝ) =>
        fourier (-n) (θ : AddCircle P) • f (r, (θ : AddCircle P))) hc isCompact_Icc
  have hint : Continuous (fun r : ℝ => ∫ θ in (0 : ℝ)..P,
      fourier (-n) (θ : AddCircle P) • f (r, (θ : AddCircle P))) := by
    simpa only [intervalIntegral.integral_of_le (Fact.out : 0 < P).le,
      integral_Icc_eq_integral_Ioc] using hi
  have heq : cylinderAngularCoefficient f n = fun r : ℝ =>
      (1 / P) • ∫ θ in (0 : ℝ)..P,
        fourier (-n) (θ : AddCircle P) • f (r, (θ : AddCircle P)) := by
    funext r
    rw [cylinderAngularCoefficient_apply, fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
  rw [heq]
  simpa only [Pi.smul_apply] using
    (show Continuous (fun _ : ℝ => (1 / P : ℝ)) from continuous_const).smul hint

/-- A single angular coefficient is bounded by the full angular `L²` energy. -/
theorem cylinderAngularCoefficient_sq_le {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) (n : ℤ) (r : ℝ) :
    ‖cylinderAngularCoefficient f n r‖ ^ 2 ≤
      ∫ θ : AddCircle P, ‖f (r, θ)‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let fr : C(AddCircle P, ℂ) :=
    ⟨fun θ => f (r, θ), hf.comp (continuous_const.prodMk continuous_id)⟩
  exact le_hasSum (circle_hasSum_sq_fourierCoeff fr) n (fun _ _ => sq_nonneg _)

/-- Each angular mode belongs to the actual radial `L²` space. -/
theorem cylinderAngularCoefficient_memLp {f : ℝ × AddCircle P → ℂ}
    (hf : Continuous f) (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) (n : ℤ) :
    MemLp (cylinderAngularCoefficient f n) 2 (volume : Measure ℝ) := by
  have hc := continuous_cylinderAngularCoefficient hf n
  have hs : Integrable (fun p : ℝ × AddCircle P => ‖f p‖ ^ 2)
      (volume.prod AddCircle.haarAddCircle) :=
    hL2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hi : Integrable
      (fun r : ℝ => ∫ θ : AddCircle P, ‖f (r, θ)‖ ^ 2 ∂AddCircle.haarAddCircle) volume :=
    hs.integral_prod_left
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply hi.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with r
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact cylinderAngularCoefficient_sq_le hf n r

/-- The radial Fourier transform of one actual angular mode. -/
def cylinderFourierMode (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) (n : ℤ) : Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕 ((cylinderAngularCoefficient_memLp hf hL2 n).toLp (cylinderAngularCoefficient f n))

/-- The concrete mixed Fourier transform of the cylinder function. -/
def cylinderFourier (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) (ζ : ℝ × ℤ) : ℂ :=
  cylinderFourierMode f hf hL2 ζ.2 ζ.1

@[simp] theorem cylinderFourier_apply (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) (ζ : ℝ × ℤ) :
    cylinderFourier f hf hL2 ζ = cylinderFourierMode f hf hL2 ζ.2 ζ.1 := rfl

/-- Plancherel in the radial variable, with the actual angular coefficient
as input and no integrability beyond `L²`. -/
theorem norm_cylinderFourierMode (f : ℝ × AddCircle P → ℂ) (hf : Continuous f)
    (hL2 : MemLp f 2 (cylinderPhysicalMeasure P)) (n : ℤ) :
    ‖cylinderFourierMode f hf hL2 n‖ =
      (eLpNorm (cylinderAngularCoefficient f n) 2 (volume : Measure ℝ)).toReal := by
  exact (Lp.norm_fourier_eq _).trans (Lp.norm_toLp _ _)

end ContinuousFlexibility.Analysis
