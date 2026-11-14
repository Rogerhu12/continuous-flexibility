module

public import ContinuousFlexibility.Radial.FourierUniqueness
public import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# Completeness of the actual physical angular coefficients

Physical L² membership supplies L² angular slices on one common radial
full-measure set. Countability makes all positive even cosine identities
available on that same set. Angular completeness and Fubini then identify
the original physical representatives.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

noncomputable section

open Set MeasureTheory
open ContinuousFlexibility.Statements

/-- Fubini applied to both measurability and the actual square integral. -/
theorem r11b_memLp_product_sections
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ r ∂μ, MemLp (fun θ => f (r, θ)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
    with r hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

/-- The converse Fubini step retains joint L² measurability. This condition
cannot be discarded for arbitrary functions with a.e. equal sections. -/
theorem r11b_memLp_ae_eq_of_sections
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f g : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν))
    (hfg : ∀ᵐ r ∂μ, (fun θ => f (r, θ)) =ᵐ[ν] (fun θ => g (r, θ))) :
    f =ᵐ[μ.prod ν] g := by
  have hsq : Integrable (fun z => (f z - g z) ^ 2) (μ.prod ν) :=
    (hf.sub hg).integrable_sq
  have hinner : (fun r => ∫ θ, (f (r, θ) - g (r, θ)) ^ 2 ∂ν) =ᵐ[μ] 0 := by
    filter_upwards [hfg] with r hr
    apply integral_eq_zero_of_ae
    filter_upwards [hr] with θ hθ
    change (f (r, θ) - g (r, θ)) ^ 2 = 0
    simp only [hθ, sub_self, zero_pow (by decide : 2 ≠ 0)]
  have hint : (∫ z, (f z - g z) ^ 2 ∂μ.prod ν) = 0 := by
    rw [integral_prod _ hsq]
    exact integral_eq_zero_of_ae hinner
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun z => sq_nonneg (f z - g z)) hsq).mp hint
  filter_upwards [hae] with z hz
  change (f z - g z) ^ 2 = 0 at hz
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem r11b_physical_memLp_angular_sections {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      MemLp (fun θ => f (r, θ)) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  rw [r11b_radialPhysicalMeasure_eq_prod] at hf
  exact r11b_memLp_product_sections hf

/-- The mean and all positive even cosine modes determine an actual physical
L² field whose angular representatives are pointwise even and π-periodic. -/
theorem r11b_physical_ae_eq_of_referenceModes {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : MemLp f 2 (radialPhysicalMeasure D)) (hg : MemLp g 2 (radialPhysicalMeasure D))
    (hfe : ∀ r, Function.Even (fun θ => f (r, θ)))
    (hge : ∀ r, Function.Even (fun θ => g (r, θ)))
    (hfp : ∀ r, Function.Periodic (fun θ => f (r, θ)) Real.pi)
    (hgp : ∀ r, Function.Periodic (fun θ => g (r, θ)) Real.pi)
    (hmean : (fun r => radialAngularMean (fun θ => f (r, θ)))
      =ᵐ[volume.restrict (radialCore D)] (fun r => radialAngularMean (fun θ => g (r, θ))))
    (hcoeff : ∀ j : ℕ, 0 < j → Even j →
      referenceMode f j =ᵐ[volume.restrict (radialCore D)] referenceMode g j) :
    f =ᵐ[radialPhysicalMeasure D] g := by
  have hall : ∀ᵐ r ∂volume.restrict (radialCore D),
      ∀ j : {j : ℕ // 0 < j ∧ Even j}, referenceMode f j r = referenceMode g j r :=
    ae_all_iff.mpr fun j => hcoeff j j.property.1 j.property.2
  have hslices : ∀ᵐ r ∂volume.restrict (radialCore D),
      (fun θ => f (r, θ)) =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
        (fun θ => g (r, θ)) := by
    filter_upwards [r11b_physical_memLp_angular_sections hf,
      r11b_physical_memLp_angular_sections hg, hmean, hall] with r hfr hgr hmr hcr
    apply even_periodic_ae_eq_of_cosine_coefficients hfr hgr
      (hfe r) (hge r) (hfp r) (hgp r)
    · simpa only [radialAngularMean, angularAverage, one_div] using hmr
    · intro j hj hjEven
      simpa only [referenceMode, radialAngularMean, angularPairing, angularAverage, one_div] using
        hcr ⟨j, hj, hjEven⟩
  rw [r11b_radialPhysicalMeasure_eq_prod] at hf hg ⊢
  exact r11b_memLp_ae_eq_of_sections hf hg hslices

end

end ContinuousFlexibility.Radial
