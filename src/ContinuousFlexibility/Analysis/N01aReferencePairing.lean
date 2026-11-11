import ContinuousFlexibility.Analysis.N01aReferenceSquareBounds
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Uniform testing bounds for actual radial sources

The source contract controls squares.  All estimates below therefore apply
to the actual iterated integrals even before measurability of the signed
source is known.  Its absolute value is measurable as the square root of
its integrable square.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem n01a_memLp_abs_of_integrable_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable (fun x => f x ^ 2) μ) :
    MemLp (fun x => |f x|) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => |f x|) μ := by
    simpa only [Real.sqrt_sq_eq_abs] using
      hf.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [sq_abs] using hf

theorem n01a_integral_abs_le_sqrt_square {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hf' : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := by
    simpa using n01a_memLp_abs_of_integrable_sq hf
  have h1 : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two h1 hf'
  simpa only [norm_one, one_mul, Real.norm_eq_abs, abs_abs, Real.rpow_two,
    sq_abs, one_pow, integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using h

/-- An iterated physical pairing is bounded using only integrability of the
absolute source. No measurability hypothesis on the signed pairing is needed. -/
theorem abs_radial_pairing_le_integral_abs {D : ReferenceData} (hab : D.a ≤ D.b)
    {f ψ : PolarPoint → ℝ} (hf : Integrable (fun p => |f p|) (radialPhysicalMeasure D))
    {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ p, |ψ p| ≤ B) :
    |∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * ψ (r, θ))| ≤
      (2 * Real.pi)⁻¹ * B * ∫ p, |f p| ∂radialPhysicalMeasure D := by
  have hμ := radialPhysicalMeasure_eq_prod_Ioc D
  rw [hμ] at hf
  have hinner : ∀ᵐ r ∂volume.restrict (Ioc D.a D.b),
      |∫ θ in Ioc (0 : ℝ) (2 * Real.pi), f (r, θ) * ψ (r, θ)| ≤
        B * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), |f (r, θ)| := by
    filter_upwards [hf.prod_right_ae] with r hr
    have h := norm_integral_le_of_norm_le (hr.const_mul B)
      (Eventually.of_forall fun θ => show ‖f (r, θ) * ψ (r, θ)‖ ≤ B * |f (r, θ)| from by
        rw [Real.norm_eq_abs, abs_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hψ (r, θ)) (abs_nonneg _))
    simpa only [Real.norm_eq_abs, integral_const_mul] using h
  have houter := norm_integral_le_of_norm_le
    (f := fun r => ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), f (r, θ) * ψ (r, θ))
    (hf.integral_prod_left.const_mul B)
    (hinner.mono fun r hr => by simpa only [Real.norm_eq_abs] using hr)
  have houter' :
      |∫ r in Ioc D.a D.b, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        f (r, θ) * ψ (r, θ)| ≤ B * ∫ p, |f p| ∂radialPhysicalMeasure D := by
    rw [hμ, MeasureTheory.integral_prod _ hf]
    simpa only [Real.norm_eq_abs, integral_const_mul] using houter
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi)),
    intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left houter' (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi))

/-- Uniform bounded tests are continuous for the actual source norm, including
the compact cutoff tests used to approach the flat reference eigenfunction. -/
theorem exists_source_pairing_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) (hD : RadialPartition D) {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : RadialSource, SourceMember D γ M F →
      ∀ (ψ : PolarPoint → ℝ) (B : ℝ), 0 ≤ B → (∀ p, |ψ p| ≤ B) →
      |∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ) * ψ (r, θ))| ≤
        C * B * Real.sqrt (sourceNormSquare D γ M F) := by
  obtain ⟨K, hK, hphysical⟩ := exists_source_physical_square_bound hab hD hγ M
  let C : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt ((radialPhysicalMeasure D).real univ) * Real.sqrt K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨1 + C, by linarith only [hC], fun F hF ψ B hB hψ => ?_⟩
  obtain ⟨hi, hb⟩ := hphysical F hF
  have ha : Integrable (fun p => |F.1 p|) (radialPhysicalMeasure D) :=
    (n01a_memLp_abs_of_integrable_sq hi).integrable (by norm_num)
  have hsqrt := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul hK.le] at hsqrt
  calc
    _ ≤ (2 * Real.pi)⁻¹ * B * ∫ p, |F.1 p| ∂radialPhysicalMeasure D :=
      abs_radial_pairing_le_integral_abs hab ha hB hψ
    _ ≤ (2 * Real.pi)⁻¹ * B *
        (Real.sqrt ((radialPhysicalMeasure D).real univ) *
          Real.sqrt (∫ p, F.1 p ^ 2 ∂radialPhysicalMeasure D)) :=
      mul_le_mul_of_nonneg_left (n01a_integral_abs_le_sqrt_square hi) (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * B *
        (Real.sqrt ((radialPhysicalMeasure D).real univ) *
          (Real.sqrt K * Real.sqrt (sourceNormSquare D γ M F))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) (by positivity)
    _ = C * B * Real.sqrt (sourceNormSquare D γ M F) := by dsimp only [C]; ring
    _ ≤ (1 + C) * B * Real.sqrt (sourceNormSquare D γ M F) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) hB) (Real.sqrt_nonneg _)

end ContinuousFlexibility.Statements
