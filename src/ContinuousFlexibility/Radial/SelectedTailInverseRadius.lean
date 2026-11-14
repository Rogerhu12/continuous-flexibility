module

public import ContinuousFlexibility.Radial.SelectedTailRadiusMeasure
public import ContinuousFlexibility.Radial.SelectedReferenceEquation
public import ContinuousFlexibility.Radial.ModeWeakLinearity
public import ContinuousFlexibility.Analysis.L2MeasureCongr

/-!
# The actual unitary transport of a tail inverse to the selected reference

The profile law gives the measure factor β after the radial Jacobian.
Consequently the unitary pullback is √β times composition with κ. The
normalized Jacobi expression is unchanged by that same coordinate law.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

private theorem inverseRadius_embedding {κ : ℝ} (hκ : κ ≠ 0) :
    MeasurableEmbedding (fun r : ℝ => κ * r) :=
  (Homeomorph.mulLeft₀ κ hκ).toMeasurableEquiv.measurableEmbedding

private theorem inverseRadius_leftInverse {κ : ℝ} (hκ : κ ≠ 0) :
    Function.LeftInverse (fun r : ℝ => r / κ) (fun r => κ * r) :=
  fun r => mul_div_cancel_left₀ r hκ

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
  rw [hm, Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hβ))]
  exact (inverseRadius_embedding hκ).ae_map_iff

/-- Eliminate the measure equality before substituting physical data. -/
private theorem inverseRadius_coordinate_cast_ae {μ ν : Measure ℝ}
    (R X : ℝ → ℝ) (hR : MeasurableEmbedding R) (hX : Function.LeftInverse X R)
    (h : ν = Measure.map R μ) (f : Lp ℝ 2 ν) :
    (l2EquivSeal ((l2MeasureCongr h).trans (coordinateL2Equiv μ R X hR hX)) f
      : ℝ → ℝ) =ᵐ[μ] fun x => f (R x) := by
  subst ν
  rw [l2EquivSeal_eq]
  exact coordinateL2Equiv_ae μ R X hR hX f

/-- The original coordinate factor, sealed with its exact equality
certificate so later kernel checks do not reduce its measure cast. -/
private def inverseRadiusCoordinateEquiv {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 (squareDensityMeasure μ (fun _ => sqrt β)) :=
  l2EquivSeal
    ((l2MeasureCongr (inverseRadius_square_measure hκ hβ hm).symm).trans
      (coordinateL2Equiv (squareDensityMeasure μ (fun _ => sqrt β))
        (fun r => κ * r) (fun r => r / κ) (inverseRadius_embedding hκ)
        (inverseRadius_leftInverse hκ)))

private theorem inverseRadiusCoordinateEquiv_ae {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) (f : Lp ℝ 2 ν) :
    (inverseRadiusCoordinateEquiv hκ hβ hm f : ℝ → ℝ)
      =ᵐ[squareDensityMeasure μ (fun _ => sqrt β)] fun r => f (κ * r) :=
  inverseRadius_coordinate_cast_ae
    (μ := squareDensityMeasure μ (fun _ => sqrt β)) (ν := ν)
    (fun r => κ * r) (fun r => r / κ) (inverseRadius_embedding hκ)
    (inverseRadius_leftInverse hκ) (inverseRadius_square_measure hκ hβ hm).symm f

/-- The original positive square-density factor with the same equality
certificate used by the physical tail gauge isometry. -/
private def inverseRadiusDensityEquiv (μ : Measure ℝ) {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (squareDensityMeasure μ (fun _ => sqrt β)) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  l2EquivSeal (squareDensityEquiv μ measurable_const (fun _ => sqrt_pos.mpr hβ))

private theorem inverseRadiusDensityEquiv_ae (μ : Measure ℝ) {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (squareDensityMeasure μ (fun _ => sqrt β))) :
    (inverseRadiusDensityEquiv μ hβ f : ℝ → ℝ) =ᵐ[μ] fun r => sqrt β * f r := by
  rw [inverseRadiusDensityEquiv, l2EquivSeal_eq]
  exact squareDensityEquiv_ae μ measurable_const (fun _ => sqrt_pos.mpr hβ) f

/-- The coordinate and square-density maps are genuine isometries on the
actual L² classes. Their exact composition certificate keeps the concrete
measure casts out of subsequent application and inverse calculations. -/
def inverseRadiusEquiv {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Classical.choose (exists_l2EquivCompose_apply
    (μ := ν) (ν := squareDensityMeasure μ (fun _ => sqrt β)) (κ := μ)
    (inverseRadiusCoordinateEquiv hκ hβ hm) (inverseRadiusDensityEquiv μ hβ))

private theorem inverseRadiusEquiv_apply {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) (f : Lp ℝ 2 ν) :
    inverseRadiusEquiv hκ hβ hm f =
      inverseRadiusDensityEquiv μ hβ (inverseRadiusCoordinateEquiv hκ hβ hm f) :=
  Classical.choose_spec (exists_l2EquivCompose_apply
    (μ := ν) (ν := squareDensityMeasure μ (fun _ => sqrt β)) (κ := μ)
    (inverseRadiusCoordinateEquiv hκ hβ hm) (inverseRadiusDensityEquiv μ hβ)) f

theorem inverseRadiusEquiv_ae {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r)) (f : Lp ℝ 2 ν) :
    (inverseRadiusEquiv hκ hβ hm f : ℝ → ℝ) =ᵐ[μ]
      fun r => sqrt β * f (κ * r) := by
  rw [inverseRadiusEquiv_apply]
  have hc := squareDensity_ae_eq μ measurable_const (fun _ => sqrt_pos.mpr hβ)
    (inverseRadiusCoordinateEquiv_ae hκ hβ hm f)
  have hg := inverseRadiusDensityEquiv_ae μ hβ (inverseRadiusCoordinateEquiv hκ hβ hm f)
  filter_upwards [hc, hg] with r hr hs
  exact hs.trans (congrArg (fun t => sqrt β * t) hr)

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
  exact (inverseRadius_ae_iff hκ hβ hm).mpr halong

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

private theorem inverseRadius_conjugate_apply {μ ν : Measure ℝ}
    (E : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 ν) :
    (E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (R.comp E.toContinuousLinearEquiv.toContinuousLinearMap)) f =
        E.symm (R (E f)) := rfl

theorem inverseRadiusOperator_apply {μ ν : Measure ℝ} {κ β : ℝ}
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 ν) :
    inverseRadiusOperator hκ hβ hm R f =
      (inverseRadiusEquiv hκ hβ hm).symm (R (inverseRadiusEquiv hκ hβ hm f)) :=
  inverseRadius_conjugate_apply (inverseRadiusEquiv hκ hβ hm) R f

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
