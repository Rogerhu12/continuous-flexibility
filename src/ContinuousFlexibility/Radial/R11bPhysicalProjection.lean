module

public import ContinuousFlexibility.Radial.FiniteFourierProjection
public import ContinuousFlexibility.Radial.R11bAngularL2Bridge
public import ContinuousFlexibility.Radial.R11bTensorL2

/-!
# Finite angular projection in the actual physical L² space

The coefficient functions are ordinary angular integrals. Fubini gives
almost-everywhere interval L² sections, so the finite angular contraction
integrates to the physical product measure without extra regularity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

def r11bFiniteProjection {ι : Type*} (s : Finset ι) (e : ι → ℝ → ℝ)
    (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  finiteAngularProjection s e (fun θ => f (x.1, θ)) x.2

theorem r11b_physical_sections_memLp {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      MemLp (fun θ => f (r, θ)) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hp : MemLp f 2 (((volume : Measure ℝ).restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [← r11b_radialPhysicalMeasure_eq_prod]
    exact hf
  filter_upwards [hp.aestronglyMeasurable.prodMk_left, hp.integrable_sq.prod_right_ae]
    with r hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

theorem r11b_finiteProjection_memLp {D : ReferenceData} {ι : Type*}
    (s : Finset ι) (e : ι → ℝ → ℝ) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    MemLp (r11bFiniteProjection s e f) 2 (radialPhysicalMeasure D) := by
  have hc (i : ι) (hi : i ∈ s) :
      MemLp (fun r => angularPairing (fun θ => f (r, θ)) (e i))
        2 (volume.restrict (radialCore D)) :=
    (r11b_memLp_angularCoefficient hf (memLp_angularMeanMeasure (he i hi))).1
  have ht (i : ι) (hi : i ∈ s) :
      MemLp (fun z : PolarPoint =>
        angularPairing (fun θ => f (z.1, θ)) (e i) * e i z.2)
        2 (radialPhysicalMeasure D) := by
    rw [r11b_radialPhysicalMeasure_eq_prod]
    exact r11b_memLp_tensor (hc i hi) (he i hi)
  have hsum := memLp_finsetSum s ht
  apply MemLp.ae_eq _ hsum
  exact Filter.Eventually.of_forall fun z => by
    simp only [Finset.sum_apply, r11bFiniteProjection, finiteAngularProjection]

theorem r11b_angular_square_integral {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    Integrable (fun r => angularAverage (fun θ => f (r, θ) ^ 2))
      (volume.restrict (radialCore D)) ∧
    (∫ r, angularAverage (fun θ => f (r, θ) ^ 2) ∂volume.restrict (radialCore D)) =
      (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  have hp := r11b_memLp_radial_angularMean hf
  refine ⟨?_, ?_⟩
  · have h := hp.integrable_sq.integral_prod_left
    simpa only [← angularAverage_eq_integral_angularMeanMeasure] using h
  · calc
      (∫ r, angularAverage (fun θ => f (r, θ) ^ 2) ∂volume.restrict (radialCore D)) =
          ∫ z, f z ^ 2 ∂((volume : Measure ℝ).restrict (radialCore D)).prod
            angularMeanMeasure := by
        simp_rw [angularAverage_eq_integral_angularMeanMeasure]
        exact (integral_prod _ hp.integrable_sq).symm
      _ = (1 / (2 * Real.pi)) * ∫ z, f z ^ 2 ∂radialPhysicalMeasure D :=
        r11b_integral_sq_radial_angularMean D f

theorem r11b_physical_square_integral_le_of_angular {D : ReferenceData}
    {f g : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D))
    (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hpoint : ∀ᵐ r ∂volume.restrict (radialCore D),
      angularAverage (fun θ => g (r, θ) ^ 2) ≤
        angularAverage (fun θ => f (r, θ) ^ 2)) :
    (∫ z, g z ^ 2 ∂radialPhysicalMeasure D) ≤
      ∫ z, f z ^ 2 ∂radialPhysicalMeasure D := by
  obtain ⟨hgi, hgeq⟩ := r11b_angular_square_integral hg
  obtain ⟨hfi, hfeq⟩ := r11b_angular_square_integral hf
  have h : (∫ r, angularAverage (fun θ => g (r, θ) ^ 2)
      ∂volume.restrict (radialCore D)) ≤
        ∫ r, angularAverage (fun θ => f (r, θ) ^ 2)
          ∂volume.restrict (radialCore D) :=
    integral_mono_ae hgi hfi hpoint
  rw [hgeq, hfeq] at h
  exact le_of_not_gt fun hgt =>
    (not_lt_of_ge h) (mul_lt_mul_of_pos_left hgt
      (by positivity : 0 < 1 / (2 * Real.pi)))

theorem r11b_finiteProjection_angular_square_le {D : ReferenceData}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      angularAverage (fun θ => r11bFiniteProjection s e f (r, θ) ^ 2) ≤
        angularAverage (fun θ => f (r, θ) ^ 2) := by
  filter_upwards [r11b_physical_sections_memLp hf] with r hr
  change angularAverage (fun θ => finiteAngularProjection s e (fun φ => f (r, φ)) θ ^ 2) ≤
    angularAverage (fun θ => f (r, θ) ^ 2)
  exact finiteAngularProjection_square_le s e hr he horth

theorem r11b_finiteProjection_square_integral_le {D : ReferenceData}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D))
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    (∫ z, r11bFiniteProjection s e f z ^ 2 ∂radialPhysicalMeasure D) ≤
      ∫ z, f z ^ 2 ∂radialPhysicalMeasure D :=
  r11b_physical_square_integral_le_of_angular (D := D) (f := f)
    (g := r11bFiniteProjection s e f) hf
    (r11b_finiteProjection_memLp (D := D) s e hf he)
    (r11b_finiteProjection_angular_square_le (D := D) s e hf he horth)

end ContinuousFlexibility.Radial
