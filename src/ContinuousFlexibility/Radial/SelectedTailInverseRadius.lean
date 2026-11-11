import ContinuousFlexibility.Radial.SelectedTailRadiusMeasure
import ContinuousFlexibility.Radial.SelectedReferenceEquation
import ContinuousFlexibility.Radial.ModeWeakLinearity
import ContinuousFlexibility.Analysis.L2MeasureCongr

/-!
# The actual unitary transport of a tail inverse to the selected reference

The profile law gives the measure factor β after the radial Jacobian.
Consequently the unitary pullback is √β times composition with κ. The
normalized Jacobi expression is unchanged by that same coordinate law.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

private theorem inverseRadius_embedding {κ : ℝ} (hκ : κ ≠ 0) :
    MeasurableEmbedding (fun r : ℝ => κ * r) :=
  (Homeomorph.mulLeft₀ κ hκ).toMeasurableEquiv.measurableEmbedding

private theorem inverseRadius_square_measure {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) :
    Measure.map (fun r => κ * r) (squareDensityMeasure μ (fun _ => sqrt β)) = ν := by
  rw [squareDensityMeasure, sq_sqrt hβ.le, withDensity_const,
    Measure.map_smul _ (inverseRadius_embedding hκ).measurable.aemeasurable]
  exact hm.symm

theorem inverseRadius_ae_iff {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) {p : ℝ → Prop} :
    (∀ᵐ x ∂ν, p x) ↔ ∀ᵐ r ∂μ, p (κ * r) := by
  rw [hm, ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hβ)),
    ae_iff, (inverseRadius_embedding hκ).map_apply, ae_iff]

/-- The coordinate and square-density maps are genuine isometries on the
actual L² classes; neither a source representative nor an inverse is assumed. -/
def inverseRadiusEquiv {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  l2EquivCompose
    (l2EquivCompose (l2MeasureCongr (inverseRadius_square_measure hκ hβ hm).symm)
      (coordinateL2Equiv (squareDensityMeasure μ (fun _ => sqrt β))
        (fun r => κ * r) (fun r => r / κ) (inverseRadius_embedding hκ)
        (fun r => by field_simp [hκ] <;> ring)))
    (squareDensityEquiv μ measurable_const (fun _ => sqrt_pos.mpr hβ))

theorem inverseRadiusEquiv_ae {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) (f : Lp ℝ 2 ν) :
    (inverseRadiusEquiv hκ hβ hm f : ℝ → ℝ) =ᵐ[μ]
      fun r => sqrt β * f (κ * r) := by
  let σ := squareDensityMeasure μ (fun _ => sqrt β)
  let M := l2MeasureCongr (inverseRadius_square_measure hκ hβ hm).symm
  let C := coordinateL2Equiv σ (fun r => κ * r) (fun r => r / κ)
    (inverseRadius_embedding hκ) (fun r => by field_simp [hκ] <;> ring)
  have hC : (C (M f) : ℝ → ℝ) =ᵐ[σ] fun r => f (κ * r) :=
    (coordinateL2Equiv_ae σ (fun r => κ * r) (fun r => r / κ)
      (inverseRadius_embedding hκ) (fun r => by field_simp [hκ] <;> ring) (M f)).trans
      (ae_eq_comp (inverseRadius_embedding hκ).measurable.aemeasurable
        (l2MeasureCongr_ae (inverseRadius_square_measure hκ hβ hm).symm f))
  have hC' := squareDensity_ae_eq μ measurable_const (fun _ => sqrt_pos.mpr hβ) hC
  have hG := squareDensityEquiv_ae μ measurable_const (fun _ => sqrt_pos.mpr hβ) (C (M f))
  rw [inverseRadiusEquiv, l2EquivCompose_apply, l2EquivCompose_apply]
  filter_upwards [hG, hC'] with r hr hc
  rw [hr, hc]

theorem inverseRadiusEquiv_ae_of_ae {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    {f : Lp ℝ 2 ν} {u : ℝ → ℝ} (hf : (f : ℝ → ℝ) =ᵐ[ν] u) :
    (inverseRadiusEquiv hκ hβ hm f : ℝ → ℝ) =ᵐ[μ]
      fun r => sqrt β * u (κ * r) := by
  filter_upwards [inverseRadiusEquiv_ae hκ hβ hm f,
    (inverseRadius_ae_iff hκ hβ hm).mp hf] with r hr hu
  rw [hr, hu]

theorem inverseRadiusEquiv_symm_ae {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) (f : Lp ℝ 2 μ) :
    ((inverseRadiusEquiv hκ hβ hm).symm f : ℝ → ℝ) =ᵐ[ν]
      radialRadiusScale κ (1 / sqrt β) (f : ℝ → ℝ) := by
  let E := inverseRadiusEquiv hκ hβ hm
  have he := inverseRadiusEquiv_ae hκ hβ hm (E.symm f)
  rw [show inverseRadiusEquiv hκ hβ hm = E from rfl, E.apply_symm_apply] at he
  have halong : (fun r => E.symm f (κ * r)) =ᵐ[μ]
      fun r => radialRadiusScale κ (1 / sqrt β) (f : ℝ → ℝ) (κ * r) := by
    filter_upwards [he] with r hr
    rw [radialRadiusScale_apply_mul hκ, hr]
    field_simp [(sqrt_pos.mpr hβ).ne']
  have halong' : (fun r => E.symm f (κ * r)) =ᵐ[squareDensityMeasure μ (fun _ => sqrt β)]
      fun r => radialRadiusScale κ (1 / sqrt β) (f : ℝ → ℝ) (κ * r) :=
    (withDensity_absolutelyContinuous μ _).ae_eq halong
  have hmap : (E.symm f : ℝ → ℝ) =ᵐ[Measure.map (fun r => κ * r)
      (squareDensityMeasure μ (fun _ => sqrt β))]
      radialRadiusScale κ (1 / sqrt β) (f : ℝ → ℝ) := by
    rw [ae_iff, (inverseRadius_embedding hκ).map_apply]
    exact ae_iff.mp halong'
  rwa [inverseRadius_square_measure hκ hβ hm] at hmap

theorem inverseRadiusEquiv_symm_ae_of_ae {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    {f : Lp ℝ 2 μ} {u : ℝ → ℝ} (hf : (f : ℝ → ℝ) =ᵐ[μ] u) :
    ((inverseRadiusEquiv hκ hβ hm).symm f : ℝ → ℝ) =ᵐ[ν]
      radialRadiusScale κ (1 / sqrt β) u := by
  apply (inverseRadius_ae_iff hκ hβ hm).mpr
  filter_upwards [(inverseRadius_ae_iff hκ hβ hm).mp
    (inverseRadiusEquiv_symm_ae hκ hβ hm f), hf] with r hr hu
  rw [radialRadiusScale_apply_mul hκ] at hr ⊢
  rw [hr, hu]

def inverseRadiusOperator {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (inverseRadiusEquiv hκ hβ hm).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.comp (inverseRadiusEquiv hκ hβ hm).toContinuousLinearEquiv.toContinuousLinearMap)

theorem inverseRadiusOperator_apply {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 ν) :
    inverseRadiusOperator hκ hβ hm R f =
      (inverseRadiusEquiv hκ hβ hm).symm (R (inverseRadiusEquiv hκ hβ hm f)) := rfl

def selectedTailRadiusEquiv {D E : ReferenceData} {κ β cut : ℝ} {right : Bool}
    (hκ : 0 < κ) (hβ : 0 < β) (hD : cut ∈ radialCore D)
    (hE : κ * cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r) :
    Lp ℝ 2 ((radialHilbertMeasure E).restrict (radialTailInterval E right (κ * cut))) ≃ₗᵢ[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) :=
  inverseRadiusEquiv hκ.ne' hβ
    (radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hD hE hend hprofile)

theorem matchingJacobiTest_radiusScale {D E : ReferenceData} {κ β r : ℝ}
    {I : Set ℝ} (hκ : κ ≠ 0) (hβ : β ≠ 0) (hI : IsOpen I) (hr : r ∈ I)
    (hprofile : ∀ t ∈ I, E.w (κ * t) = (β * κ) * D.w t)
    (j : ℕ) (ψ : ℝ → ℝ) :
    matchingJacobiTest E j ψ (κ * r) =
      matchingJacobiTest D j (fun t => ψ (κ * t)) r := by
  have he : radialRadiusScale κ 1 (fun t => ψ (κ * t)) = ψ := by
    funext t
    have hcancel : κ * (t / κ) = t := by field_simp [hκ] <;> ring
    simp only [radialRadiusScale, one_mul, hcancel]
  have hJ := radialJacobi_reference_radiusScale hκ hI hr hprofile
    ((j : ℝ) ^ 2) 1 (fun t => ψ (κ * t))
  rw [he, mul_one] at hJ
  have hρ : matchingDensity E (κ * r) = (β / κ) * matchingDensity D r := by
    unfold matchingDensity
    rw [hprofile r hr]
    by_cases hr0 : r = 0
    · simp [hr0]
    · field_simp [hκ, hr0] <;> ring
  rw [matchingJacobiTest, hJ, hρ]
  exact mul_div_mul_left _ _ (div_ne_zero hβ hκ)

end ContinuousFlexibility.Radial
