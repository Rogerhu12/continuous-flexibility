import ContinuousFlexibility.Radial.R11bPhysicalProjection

/-!
# Cell Bessel bounds for the original angular coefficients

The localizer commutes exactly with each ordinary angular coefficient.
Consequently finite Bessel inequalities apply directly to every actual
localized L² field, with no global regularity premise on the original field.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_angularPairing_const_mul (c : ℝ) (f g : ℝ → ℝ) :
    angularPairing (fun θ => c * f θ) g = c * angularPairing f g := by
  unfold angularPairing angularAverage
  have h : (fun θ => (c * f θ) * g θ) = fun θ => c * (f θ * g θ) :=
    funext (fun θ => mul_assoc _ _ _)
  rw [h, intervalIntegral.integral_const_mul]
  ring

theorem r11b_physical_finite_bessel {D : ReferenceData}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    (∑ i ∈ s, ∫ r, angularPairing (fun θ => f (r, θ)) (e i) ^ 2
      ∂volume.restrict (radialCore D)) ≤
      (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  have hc (i : ι) (hi : i ∈ s) :
      Integrable (fun r => angularPairing (fun θ => f (r, θ)) (e i) ^ 2)
        (volume.restrict (radialCore D)) :=
    (r11b_memLp_angularCoefficient hf (memLp_angularMeanMeasure (he i hi))).1.integrable_sq
  obtain ⟨hfi, hfeq⟩ := r11b_angular_square_integral hf
  have hpoint : ∀ᵐ r ∂volume.restrict (radialCore D),
      (∑ i ∈ s, angularPairing (fun θ => f (r, θ)) (e i) ^ 2) ≤
        angularAverage (fun θ => f (r, θ) ^ 2) :=
    (r11b_physical_sections_memLp hf).mono
      (fun r hr => angularPairing_finite_bessel s e hr he horth)
  calc
    (∑ i ∈ s, ∫ r, angularPairing (fun θ => f (r, θ)) (e i) ^ 2
        ∂volume.restrict (radialCore D)) =
        ∫ r, ∑ i ∈ s, angularPairing (fun θ => f (r, θ)) (e i) ^ 2
          ∂volume.restrict (radialCore D) := (integral_finsetSum s hc).symm
    _ ≤ ∫ r, angularAverage (fun θ => f (r, θ) ^ 2)
        ∂volume.restrict (radialCore D) :=
      integral_mono_ae (integrable_finsetSum s hc) hfi hpoint
    _ = (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := hfeq

theorem r11b_cell_finite_bessel {D : ReferenceData} (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) (m : ℕ) :
    (∑ i ∈ s, ∫ r,
      (D.localizer m r * angularPairing (fun θ => f (r, θ)) (e i)) ^ 2
        ∂volume.restrict (radialCore D)) ≤ referenceCellSquare D m f := by
  have h := r11b_physical_finite_bessel s e (hf m) he horth
  simp_rw [r11b_angularPairing_const_mul] at h
  rw [r11b_referenceCellSquare_eq_integral hab hf m]
  simpa only [one_div] using h

theorem r11b_cosine_cell_finite_bessel {D : ReferenceData} (hab : D.a ≤ D.b)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, 0 < j)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (m : ℕ) :
    (∑ j ∈ J, ∫ r, (D.localizer m r * referenceMode f j r) ^ 2
      ∂volume.restrict (radialCore D)) ≤ referenceCellSquare D m f := by
  have h := r11b_cell_finite_bessel hab J cosineMode hf
    (fun j _ => cosineMode_memLp_angularInterval j)
    (fun j hj k hk => angularPairing_cosineMode j k (hJ j hj) (hJ k hk)) m
  simpa only [referenceMode, radialAngularMean, angularPairing, angularAverage, one_div] using h

end ContinuousFlexibility.Radial
