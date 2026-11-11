import ContinuousFlexibility.Radial.ReferenceCellAlgebra
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier completeness for the actual angular sections

The coefficients are the genuine interval Fourier integrals. Parseval is
inherited from mathlib's complete Fourier Hilbert basis, and its hypotheses
are supplied by the local physical `L²` condition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal

/-- Complex Fourier coefficients on the physical angular interval. -/
def referenceAngularFourierCoeff (f : ℝ → ℝ) (n : ℤ) : ℂ :=
  fourierCoeffOn (show (0 : ℝ) < 2 * Real.pi by positivity)
    (fun θ => (f θ : ℂ)) n

theorem referenceAngularFourierCoeff_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℤ) :
    referenceAngularFourierCoeff (fun θ => c * f θ) n =
      (c : ℂ) * referenceAngularFourierCoeff f n := by
  unfold referenceAngularFourierCoeff
  simpa only [Complex.ofReal_mul] using
    fourierCoeffOn.const_mul (fun θ => (f θ : ℂ)) (c : ℂ) n
      (show (0 : ℝ) < 2 * Real.pi by positivity)

theorem referenceAngularFourierCoeff_congr_ae {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] g) :
    referenceAngularFourierCoeff f = referenceAngularFourierCoeff g := by
  apply fourierCoeffOn_congr_ae
  exact hfg.fun_comp (fun x : ℝ => (x : ℂ))

/-- Parseval with the exact angular normalization used in the reference norm. -/
theorem hasSum_sq_referenceAngularFourierCoeff {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    HasSum (fun n : ℤ => ‖referenceAngularFourierCoeff f n‖ ^ 2)
      (radialAngularMean (fun θ => f θ ^ 2)) := by
  have hc : MemLp (fun θ => (f θ : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := hf.ofReal
  simpa only [referenceAngularFourierCoeff, sub_zero, smul_eq_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, radialAngularMean] using
    hasSum_sq_fourierCoeffOn
      (show (0 : ℝ) < 2 * Real.pi by positivity) hc

theorem tsum_sq_referenceAngularFourierCoeff {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    (∑' n : ℤ, ‖referenceAngularFourierCoeff f n‖ ^ 2) =
      radialAngularMean (fun θ => f θ ^ 2) :=
  (hasSum_sq_referenceAngularFourierCoeff hf).tsum_eq

/-- Fourier uniqueness is proved from Parseval, with no reconstruction hypothesis. -/
theorem ae_eq_zero_of_referenceAngularFourierCoeff_eq_zero {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hz : ∀ n : ℤ, referenceAngularFourierCoeff f n = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] 0 := by
  have hzero : HasSum (fun n : ℤ => ‖referenceAngularFourierCoeff f n‖ ^ 2) 0 := by
    simpa [hz] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)
  have hmean := (hasSum_sq_referenceAngularFourierCoeff hf).unique hzero
  unfold radialAngularMean at hmean
  have hden : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hi : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ ^ 2) = 0 :=
    (mul_eq_zero.mp hmean).resolve_left hden
  rw [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] at hi
  have hae : (fun θ => f θ ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun θ => sq_nonneg (f θ)) hf.integrable_sq).mp hi
  filter_upwards [hae] with θ hθ
  exact sq_eq_zero_iff.mp hθ

/-- Fubini for the `L²` condition, retaining angular measurability. -/
theorem memLp_two_prod_sections {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ r ∂μ, MemLp (fun θ => f (r, θ)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    hf.integrable_sq.prod_right_ae] with r hrm hri
  exact (memLp_two_iff_integrable_sq hrm).2 hri

theorem RadialCellIntegrable.ae_angular_memLp
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hD : RadialPartition D) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      MemLp (fun θ => f (r, θ)) 2
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hslice (m : ℕ) :
      ∀ᵐ r ∂volume.restrict (radialCore D),
        MemLp (fun θ => D.localizer m r * f (r, θ)) 2
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    have hm : MemLp (fun x : PolarPoint => D.localizer m x.1 * f x) 2
        ((volume.restrict (radialCore D)).prod
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
      simpa only [radialPhysicalMeasure_eq_prod] using hf m
    exact memLp_two_prod_sections hm
  have hall :
      ∀ᵐ r ∂volume.restrict (radialCore D), ∀ m : ℕ,
        MemLp (fun θ => D.localizer m r * f (r, θ)) 2
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    ae_all_iff.2 hslice
  have hmem : ∀ᵐ r ∂volume.restrict (radialCore D), r ∈ radialCore D :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hall, hmem] with r hr hrmem
  obtain ⟨m, hm⟩ := hD.exists_localizer_ne_zero hrmem
  simpa only [← mul_assoc, inv_mul_cancel₀ hm, one_mul] using
    (hr m).const_mul ((D.localizer m r)⁻¹)

theorem RadialCellIntegrable.ae_angular_fourier_parseval
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hD : RadialPartition D) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      HasSum (fun n : ℤ => ‖referenceAngularFourierCoeff (fun θ => f (r, θ)) n‖ ^ 2)
        (radialAngularMean (fun θ => f (r, θ) ^ 2)) :=
  (hf.ae_angular_memLp hD).mono fun _ hr => hasSum_sq_referenceAngularFourierCoeff hr

/-- A radial localizer commutes with every Fourier coefficient, so Parseval
applies to each frozen cell square without changing its normalization. -/
theorem RadialCellIntegrable.ae_cell_fourier_parseval
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (m : ℕ) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      HasSum (fun n : ℤ => D.localizer m r ^ 2 *
        ‖referenceAngularFourierCoeff (fun θ => f (r, θ)) n‖ ^ 2)
        (radialAngularMean (fun θ => (D.localizer m r * f (r, θ)) ^ 2)) := by
  have hm : MemLp (fun x : PolarPoint => D.localizer m x.1 * f x) 2
      ((volume.restrict (radialCore D)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hf m
  filter_upwards [memLp_two_prod_sections hm] with r hr
  simpa only [referenceAngularFourierCoeff_const_mul, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      hasSum_sq_referenceAngularFourierCoeff hr

end ContinuousFlexibility.Statements
