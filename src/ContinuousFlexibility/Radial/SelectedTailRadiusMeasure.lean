import ContinuousFlexibility.Radial.SelectedReferenceTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The actual radial measure under a radius dilation

The profile law `E.w (κ*r) = β*κ*D.w r` makes the radial density
scale by `β/κ`. The Lebesgue Jacobian contributes `κ`, leaving exactly
`β` times the pushforward of the original restricted radial measure.
The proof uses the density definition, not a supplied measure identity.

The transport is a measurable equivalence. Consequently the L² statements
below do not require a separate measurability assumption on the function.
A single Boolean endpoint parameter handles the two natural tail intervals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ENNReal

private theorem selected_radius_embedding {κ : ℝ} (hκ : κ ≠ 0) :
    MeasurableEmbedding (fun r : ℝ => κ * r) :=
  (Homeomorph.mulLeft₀ κ hκ).toMeasurableEquiv.measurableEmbedding

private theorem selected_withDensity_map {f : ℝ → ℝ} (hf : MeasurableEmbedding f)
    (μ : Measure ℝ) (g : ℝ → ℝ≥0∞) :
    (μ.map f).withDensity g = (μ.withDensity (fun x => g (f x))).map f := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map,
    Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs)]

private theorem selected_volume_restrict_image {κ : ℝ} (hκ : 0 < κ) (J : Set ℝ) :
    volume.restrict ((fun r : ℝ => κ * r) '' J) =
      ENNReal.ofReal κ • (volume.restrict J).map (fun r => κ * r) := by
  have hm := selected_radius_embedding hκ.ne'
  have h := congrArg
    (fun μ : Measure ℝ => μ.restrict ((fun r : ℝ => κ * r) '' J))
    (Real.smul_map_volume_mul_left hκ.ne')
  simpa only [abs_of_pos hκ, Measure.restrict_smul, hm.restrict_map,
    hm.injective.preimage_image] using h.symm

/-- Restricting to an actual part of the core removes the redundant
restriction in the definition of the radial Hilbert measure. -/
theorem selectedRadialMeasure_restrict {D : ReferenceData} {J : Set ℝ}
    (hJ : MeasurableSet J) (hcore : J ⊆ radialCore D) :
    (radialHilbertMeasure D).restrict J =
      (volume.restrict J).withDensity (fun r => ENNReal.ofReal (12 * D.w r / r ^ 2)) := by
  rw [radialHilbertMeasure, restrict_withDensity hJ,
    Measure.restrict_restrict_of_subset hcore]

/-- The exact restricted radial-measure identity for a genuine profile
dilation. No measurability assumption on the profile is needed. -/
theorem radialHilbertMeasure_restrict_radiusScale {D E : ReferenceData}
    {κ β : ℝ} {J : Set ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hJ : MeasurableSet J) (hD : J ⊆ radialCore D)
    (hE : (fun r : ℝ => κ * r) '' J ⊆ radialCore E)
    (hprofile : ∀ r ∈ J, E.w (κ * r) = (β * κ) * D.w r) :
    (radialHilbertMeasure E).restrict ((fun r : ℝ => κ * r) '' J) =
      ENNReal.ofReal β • ((radialHilbertMeasure D).restrict J).map (fun r => κ * r) := by
  let ρD : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (12 * D.w r / r ^ 2)
  let ρE : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (12 * E.w r / r ^ 2)
  have hm := selected_radius_embedding hκ.ne'
  have himage : MeasurableSet ((fun r : ℝ => κ * r) '' J) :=
    hm.measurableSet_image.mpr hJ
  have hDmeasure : (radialHilbertMeasure D).restrict J =
      (volume.restrict J).withDensity ρD := selectedRadialMeasure_restrict hJ hD
  have hEmeasure : (radialHilbertMeasure E).restrict ((fun r : ℝ => κ * r) '' J) =
      (volume.restrict ((fun r : ℝ => κ * r) '' J)).withDensity ρE :=
    selectedRadialMeasure_restrict himage hE
  have hdensity : (fun r => ρE (κ * r)) =ᵐ[volume.restrict J]
      ENNReal.ofReal (β / κ) • ρD := by
    filter_upwards [ae_restrict_mem hJ] with r hr
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp only [ρD, ρE]
    rw [hprofile r hr]
    have halg : 12 * ((β * κ) * D.w r) / (κ * r) ^ 2 =
        (β / κ) * (12 * D.w r / r ^ 2) := by
      by_cases hr0 : r = 0
      · simp [hr0]
      · field_simp [hκ.ne', hr0] <;> ring
    rw [halg, ENNReal.ofReal_mul (div_pos hβ hκ).le]
  have hcoef : κ * (β / κ) = β := by field_simp [hκ.ne'] <;> ring
  rw [hEmeasure, selected_volume_restrict_image hκ J, withDensity_smul_measure,
    selected_withDensity_map hm, withDensity_congr_ae hdensity,
    withDensity_smul' (ENNReal.ofReal (β / κ)) ρD ENNReal.ofReal_ne_top,
    Measure.map_smul _ hm.measurable.aemeasurable, smul_smul,
    ← ENNReal.ofReal_mul hκ.le, hcoef, ← hDmeasure]

private theorem selected_memLp_smul_measure_iff {μ : Measure ℝ} {u : ℝ → ℝ}
    {β : ℝ} (hβ : 0 < β) :
    MemLp u 2 (ENNReal.ofReal β • μ) ↔ MemLp u 2 μ := by
  constructor
  · intro h
    have hback := h.smul_measure (c := ENNReal.ofReal (β⁻¹)) ENNReal.ofReal_ne_top
    simpa only [smul_smul, ← ENNReal.ofReal_mul (inv_pos.mpr hβ).le,
      inv_mul_cancel₀ hβ.ne', ENNReal.ofReal_one, one_smul] using hback
  · intro h
    exact h.smul_measure ENNReal.ofReal_ne_top

private theorem selected_memLp_const_mul_iff {μ : Measure ℝ} {u : ℝ → ℝ}
    {α : ℝ} (hα : α ≠ 0) :
    MemLp (fun r => α * u r) 2 μ ↔ MemLp u 2 μ := by
  constructor
  · intro h
    have hback := h.const_mul (α⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hα, one_mul] using hback
  · intro h
    exact h.const_mul α

private theorem selected_memLp_radius_map_iff {μ : Measure ℝ} {u : ℝ → ℝ}
    {κ β α : ℝ} (hκ : κ ≠ 0) (hβ : 0 < β) (hα : α ≠ 0) :
    MemLp (radialRadiusScale κ α u) 2
      (ENNReal.ofReal β • μ.map (fun r => κ * r)) ↔ MemLp u 2 μ := by
  rw [selected_memLp_smul_measure_iff hβ,
    (selected_radius_embedding hκ).memLp_map_measure_iff]
  have hcomp : radialRadiusScale κ α u ∘ (fun r => κ * r) =
      fun r => α * u r := by
    funext r
    exact radialRadiusScale_apply_mul hκ α u r
  rw [hcomp]
  exact selected_memLp_const_mul_iff hα

/-- The actual natural L² condition is preserved and reflected under the
radius/height dilation when the solution amplitude is nonzero. -/
theorem memLp_radialRadiusScale_restrict_image_iff {D E : ReferenceData}
    {κ β α : ℝ} {J : Set ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0)
    (hJ : MeasurableSet J) (hD : J ⊆ radialCore D)
    (hE : (fun r : ℝ => κ * r) '' J ⊆ radialCore E)
    (hprofile : ∀ r ∈ J, E.w (κ * r) = (β * κ) * D.w r) :
    MemLp (radialRadiusScale κ α u) 2
      ((radialHilbertMeasure E).restrict ((fun r : ℝ => κ * r) '' J)) ↔
      MemLp u 2 ((radialHilbertMeasure D).restrict J) := by
  rw [radialHilbertMeasure_restrict_radiusScale hκ hβ hJ hD hE hprofile]
  exact selected_memLp_radius_map_iff hκ.ne' hβ hα

/-- Forward transport allows a zero solution amplitude as well. -/
theorem memLp_radialRadiusScale_restrict_image {D E : ReferenceData}
    {κ β α : ℝ} {J : Set ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hβ : 0 < β)
    (hJ : MeasurableSet J) (hD : J ⊆ radialCore D)
    (hE : (fun r : ℝ => κ * r) '' J ⊆ radialCore E)
    (hprofile : ∀ r ∈ J, E.w (κ * r) = (β * κ) * D.w r)
    (hu : MemLp u 2 ((radialHilbertMeasure D).restrict J)) :
    MemLp (radialRadiusScale κ α u) 2
      ((radialHilbertMeasure E).restrict ((fun r : ℝ => κ * r) '' J)) := by
  by_cases hα : α = 0
  · subst α
    have hz : radialRadiusScale κ 0 u = (0 : ℝ → ℝ) := by
      funext r
      simp only [radialRadiusScale, zero_mul, Pi.zero_apply]
    rw [hz]
    exact memLp_zero
  · exact (memLp_radialRadiusScale_restrict_image_iff
      hκ hβ hα hJ hD hE hprofile).mpr hu

/-- Positivity of the radius dilation gives the exact image of an open
interval, without imposing any order on its two endpoints. -/
theorem selected_radius_image_Ioo {κ : ℝ} (hκ : 0 < κ) (l h : ℝ) :
    (fun r : ℝ => κ * r) '' Ioo l h = Ioo (κ * l) (κ * h) := by
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨mul_lt_mul_of_pos_left hs.1 hκ, mul_lt_mul_of_pos_left hs.2 hκ⟩
  · intro hr
    refine ⟨r / κ, ⟨?_, ?_⟩, ?_⟩
    · apply (lt_div_iff₀ hκ).mpr
      simpa only [mul_comm l κ] using hr.1
    · apply (div_lt_iff₀ hκ).mpr
      simpa only [mul_comm h κ] using hr.2
    · field_simp [hκ.ne'] <;> ring

theorem radialHilbertMeasure_restrict_Ioo_radiusScale {D E : ReferenceData}
    {κ β l h : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hD : Ioo l h ⊆ radialCore D) (hE : Ioo (κ * l) (κ * h) ⊆ radialCore E)
    (hprofile : ∀ r ∈ Ioo l h, E.w (κ * r) = (β * κ) * D.w r) :
    (radialHilbertMeasure E).restrict (Ioo (κ * l) (κ * h)) =
      ENNReal.ofReal β • ((radialHilbertMeasure D).restrict (Ioo l h)).map (fun r => κ * r) := by
  simpa only [selected_radius_image_Ioo hκ] using
    radialHilbertMeasure_restrict_radiusScale hκ hβ measurableSet_Ioo hD
      (by simpa only [selected_radius_image_Ioo hκ] using hE) hprofile

theorem memLp_radialRadiusScale_Ioo_iff {D E : ReferenceData}
    {κ β α l h : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0)
    (hD : Ioo l h ⊆ radialCore D) (hE : Ioo (κ * l) (κ * h) ⊆ radialCore E)
    (hprofile : ∀ r ∈ Ioo l h, E.w (κ * r) = (β * κ) * D.w r) :
    MemLp (radialRadiusScale κ α u) 2
      ((radialHilbertMeasure E).restrict (Ioo (κ * l) (κ * h))) ↔
      MemLp u 2 ((radialHilbertMeasure D).restrict (Ioo l h)) := by
  simpa only [selected_radius_image_Ioo hκ] using
    memLp_radialRadiusScale_restrict_image_iff (u := u) hκ hβ hα measurableSet_Ioo hD
      (by simpa only [selected_radius_image_Ioo hκ] using hE) hprofile

private theorem selected_tail_subset_core {D : ReferenceData} {entry : ℝ}
    (hentry : entry ∈ radialCore D) (right : Bool) :
    radialTailInterval D right entry ⊆ radialCore D := by
  cases right
  · intro r hr
    exact ⟨hr.1, hr.2.trans hentry.2⟩
  · intro r hr
    exact ⟨hentry.1.trans hr.1, hr.2⟩

/-- A single endpoint identity transports the corresponding tail; the
other endpoint of the reference need not be a dilation of the old one. -/
theorem radialTailInterval_radius_image {D E : ReferenceData} {κ entry : ℝ}
    (hκ : 0 < κ) (right : Bool)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a)) :
    (fun r : ℝ => κ * r) '' radialTailInterval D right entry =
      radialTailInterval E right (κ * entry) := by
  cases right
  · change E.a = κ * D.a at hend
    change (fun r : ℝ => κ * r) '' Ioo D.a entry = Ioo E.a (κ * entry)
    rw [selected_radius_image_Ioo hκ, hend]
  · change E.b = κ * D.b at hend
    change (fun r : ℝ => κ * r) '' Ioo entry D.b = Ioo (κ * entry) E.b
    rw [selected_radius_image_Ioo hκ, hend]

theorem radialHilbertMeasure_restrict_tail_radiusScale {D E : ReferenceData}
    {κ β entry : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (right : Bool)
    (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r) :
    (radialHilbertMeasure E).restrict (radialTailInterval E right (κ * entry)) =
      ENNReal.ofReal β • ((radialHilbertMeasure D).restrict
        (radialTailInterval D right entry)).map (fun r => κ * r) := by
  have himage := radialTailInterval_radius_image hκ right hend
  have hmeas : MeasurableSet (radialTailInterval D right entry) := by
    cases right <;> exact measurableSet_Ioo
  rw [← himage]
  exact radialHilbertMeasure_restrict_radiusScale hκ hβ hmeas
    (selected_tail_subset_core hD right)
    (by rw [himage]; exact selected_tail_subset_core hE right) hprofile

theorem memLp_radialRadiusScale_tail_iff {D E : ReferenceData}
    {κ β α entry : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hα : α ≠ 0) (right : Bool)
    (hD : entry ∈ radialCore D) (hE : κ * entry ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r) :
    MemLp (radialRadiusScale κ α u) 2
      ((radialHilbertMeasure E).restrict (radialTailInterval E right (κ * entry))) ↔
      MemLp u 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right entry)) := by
  rw [radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hD hE hend hprofile]
  exact selected_memLp_radius_map_iff hκ.ne' hβ hα

end ContinuousFlexibility.Radial
