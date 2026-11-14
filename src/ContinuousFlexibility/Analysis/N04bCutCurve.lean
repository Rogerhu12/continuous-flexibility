module

public import ContinuousFlexibility.Analysis.N04bMovingDomains
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Smooth actual travel cuts have planar measure zero

A smooth inverse on the full open travel strip gives a smooth physical
curve at every interior travel level. The whole curve has planar volume
zero, without a radial graph assumption or an injectivity assumption.

For the measure statement, extend any differentiable parametrized curve
to the planar map `(r, θ) ↦ γ θ`. Its image of one null vertical line is
the whole curve. The actual differentiable-image null-set theorem then
applies directly. Equality with the inverse supplied by `invFunOn`
transfers these conclusions to the genuine travel cut from MovingDomains.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

/-- An entire differentiable real curve has zero planar volume. -/
theorem n04b_volume_range_differentiable_curve {γ : ℝ → PolarPoint}
    (hγ : Differentiable ℝ γ) :
    (volume : Measure PolarPoint) (Set.range γ) = 0 := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hline : (volume : Measure PolarPoint)
      ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) = 0 := by
    simp only [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  have hF : Differentiable ℝ (fun p : PolarPoint => γ p.2) :=
    hγ.comp differentiable_snd
  have himage : (fun p : PolarPoint => γ p.2) ''
      ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) = Set.range γ := by
    apply Set.Subset.antisymm
    · rintro y ⟨p, _, rfl⟩
      exact ⟨p.2, rfl⟩
    · rintro y ⟨θ, rfl⟩
      exact ⟨(0, θ), ⟨mem_singleton 0, mem_univ θ⟩, rfl⟩
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume : Measure PolarPoint) hF.differentiableOn hline
  simpa only [himage] using hz

/-- Slicing a smooth map at an interior travel level is genuinely smooth. -/
theorem n04b_contDiff_travelSlice {G : PolarPoint → PolarPoint} {T t : ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun θ : ℝ => G (t, θ)) := by
  have hs : ContDiff ℝ ∞ (fun θ : ℝ => (t, θ)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using
    hG.comp_contDiff hs (fun θ => ⟨ht, mem_univ θ⟩)

/-- The image of the entire interior slice is a null physical curve. -/
theorem n04b_volume_range_travelSlice {G : PolarPoint → PolarPoint} {T t : ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (volume : Measure PolarPoint) (Set.range (fun θ : ℝ => G (t, θ))) = 0 :=
  n04b_volume_range_differentiable_curve
    ((n04b_contDiff_travelSlice hG ht).differentiable (by simp))

/-- A genuine smooth inverse identifies the actual chosen cut parametrization. -/
theorem n04b_contDiff_travelCutPoint
    {Ω : Set PolarPoint} {Γ G : PolarPoint → PolarPoint} {T t : ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hFG : ∀ p ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), Γ (G p) = p)
    (hGsmooth : ContDiffOn ℝ ∞ G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (n04bTravelCutPoint Ω Γ t) := by
  have heq : n04bTravelCutPoint Ω Γ t = fun θ : ℝ => G (t, θ) :=
    funext (n04b_travelCutPoint_eq_of_inverse hΓ hG hFG ht)
  rw [heq]
  exact n04b_contDiff_travelSlice hGsmooth ht

/-- The level-set definition, rather than an arbitrary curve, is null. -/
theorem n04b_volume_travelCut
    {Ω : Set PolarPoint} {Γ G : PolarPoint → PolarPoint} {T t : ℝ}
    (hΓ : BijOn Γ Ω (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)) Ω)
    (hFG : ∀ p ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), Γ (G p) = p)
    (hGsmooth : ContDiffOn ℝ ∞ G (Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ)))
    (ht : t ∈ Ioo (0 : ℝ) T) :
    (volume : Measure PolarPoint) (n04bTravelCut Ω Γ t) = 0 := by
  rw [← n04b_range_travelCutPoint hΓ ht]
  exact n04b_volume_range_differentiable_curve
    ((n04b_contDiff_travelCutPoint hΓ hG hFG hGsmooth ht).differentiable (by simp))

/-- Countably many genuine smooth cuts still form a planar null set. -/
theorem n04b_volume_iUnion_range_differentiable_curve
    {ι : Type*} [Countable ι] {γ : ι → ℝ → PolarPoint}
    (hγ : ∀ i, Differentiable ℝ (γ i)) :
    (volume : Measure PolarPoint) (⋃ i, Set.range (γ i)) = 0 :=
  measure_iUnion_null (fun i => n04b_volume_range_differentiable_curve (hγ i))

end ContinuousFlexibility.Analysis
