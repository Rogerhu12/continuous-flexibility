import ContinuousFlexibility.Radial.SelectedTailInverseRadius
import ContinuousFlexibility.Radial.OuterGreenIntegral
import ContinuousFlexibility.Analysis.CoordinateGaugeKernel

/-!
# The actual Green kernel of the retained-radius inverse

The inverse is the existing `inverseRadiusOperator`, with its exact
square-root-density isometry.  The height factor in the measure cancels
the height factor in the Green normalization.  Every source is an actual
L² class; no smooth-source or pointwise-integrability restriction is added.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis

variable {μ ν : Measure ℝ} {κ β : ℝ}

/-- Conjugation by the actual radius isometry preserves the operator norm. -/
theorem norm_inverseRadiusOperator
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    ‖inverseRadiusOperator hκ hβ hm R‖ = ‖R‖ := by
  let E := inverseRadiusEquiv hκ hβ hm
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
    intro f
    change ‖E.symm (R (E f))‖ ≤ ‖R‖ * ‖f‖
    rw [E.symm.norm_map]
    simpa only [E.norm_map] using R.le_opNorm (E f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have h := (inverseRadiusOperator hκ hβ hm R).le_opNorm (E.symm f)
    change ‖E.symm (R (E (E.symm f)))‖ ≤
      ‖inverseRadiusOperator hκ hβ hm R‖ * ‖E.symm f‖ at h
    simpa only [E.apply_symm_apply, E.symm.norm_map] using h

/-- The existing transported inverse has the transported kernel on all
L² sources.  The only kernel input is the original operator's identity
and the exact coordinate/height identity for the two kernels. -/
theorem inverseRadiusOperator_kernel
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    {K L : ℝ → ℝ → ℝ}
    (hR : ∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
      fun x => ∫ y, K x y * f y ∂μ)
    (hK : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, β * L (κ * x) (κ * y) = K x y)
    (f : Lp ℝ 2 ν) :
    (inverseRadiusOperator hκ hβ hm R f : ℝ → ℝ) =ᵐ[ν]
      fun x => ∫ y, L x y * f y ∂ν := by
  have hmul : MeasurableEmbedding (fun r : ℝ => κ * r) :=
    (Homeomorph.mulLeft₀ κ hκ).toMeasurableEquiv.measurableEmbedding
  have hm' : Measure.map (fun r : ℝ => κ * r)
      (squareDensityMeasure μ (fun _ => sqrt β)) = ν := by
    rw [squareDensityMeasure, sq_sqrt hβ.le, withDensity_const,
      Measure.map_smul _ hmul.measurable.aemeasurable]
    exact hm.symm
  refine coordinateGauge_operator_kernel (s := 1) hmul measurable_const
    (fun _ => sqrt_pos.mpr hβ) hm' (inverseRadiusEquiv hκ hβ hm)
    (inverseRadiusEquiv_ae hκ hβ hm) R
    (inverseRadiusOperator hκ hβ hm R) ?_ hR ?_ f
  · intro g
    rw [inverseRadiusOperator_apply, LinearIsometryEquiv.apply_symm_apply, one_smul]
  · filter_upwards [hK] with x hx
    filter_upwards [hx] with y hy
    calc
      sqrt β * sqrt β * L (κ * x) (κ * y) = β * L (κ * x) (κ * y) := by
        rw [← pow_two, sq_sqrt hβ.le]
      _ = 1 * K x y := by rw [hy, one_mul]

/-- The same two actual homogeneous solutions, precomposed by the
positive radius change, have exactly the required kernel scaling. -/
theorem outerGreenKernel_radiusScale
    (hκ : 0 < κ) (hβ : β ≠ 0) (lam : ℝ) (U V : ℝ → ℝ) (x y : ℝ) :
    β * outerGreenKernel (β * lam) (fun r => U (r / κ))
      (fun r => V (r / κ)) (κ * x) (κ * y) =
        outerGreenKernel lam U V x y := by
  have hmin : min (κ * x) (κ * y) = κ * min x y := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, min_eq_left (mul_le_mul_of_nonneg_left hxy hκ.le)]
    · rw [min_eq_right hyx, min_eq_right (mul_le_mul_of_nonneg_left hyx hκ.le)]
  have hmax : max (κ * x) (κ * y) = κ * max x y := by
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy, max_eq_right (mul_le_mul_of_nonneg_left hxy hκ.le)]
    · rw [max_eq_left hyx, max_eq_left (mul_le_mul_of_nonneg_left hyx hκ.le)]
  have hdiv (r : ℝ) : κ * r / κ = r := by field_simp [hκ.ne']
  have hfactor : β * (β * lam)⁻¹ = lam⁻¹ := by
    rw [mul_inv_rev]
    calc
      β * (lam⁻¹ * β⁻¹) = (β * β⁻¹) * lam⁻¹ := by ring
      _ = lam⁻¹ := by rw [mul_inv_cancel₀ hβ, one_mul]
  simp only [outerGreenKernel, hmin, hmax, hdiv]
  rw [← mul_assoc, hfactor]

/-- The original Green formula is retained by the actual scaled inverse,
with the actual scaled boundary parameter and the same precomposed pair. -/
theorem inverseRadiusOperator_outerGreenKernel
    (hκ : 0 < κ) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (lam : ℝ) (U V : ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ]
      fun x => ∫ y, outerGreenKernel lam U V x y * f y ∂μ)
    (f : Lp ℝ 2 ν) :
    (inverseRadiusOperator hκ.ne' hβ hm R f : ℝ → ℝ) =ᵐ[ν]
      fun x => ∫ y, outerGreenKernel (β * lam) (fun r => U (r / κ))
        (fun r => V (r / κ)) x y * f y ∂ν := by
  apply inverseRadiusOperator_kernel hκ.ne' hβ hm R hR
  exact Eventually.of_forall (fun x => Eventually.of_forall
    (fun y => outerGreenKernel_radiusScale hκ hβ.ne' lam U V x y))

/-- Pullback of the actual supplied function preserves its L² membership
under the same finite height factor, without choosing a new representative. -/
theorem memLp_inverseRadiusPullback
    (hκ : κ ≠ 0)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    {V : ℝ → ℝ} (hV : MemLp V 2 μ) :
    MemLp (fun r => V (r / κ)) 2 ν := by
  have hmul : MeasurableEmbedding (fun r : ℝ => κ * r) :=
    (Homeomorph.mulLeft₀ κ hκ).toMeasurableEquiv.measurableEmbedding
  rw [hm]
  apply MemLp.smul_measure _ ENNReal.ofReal_ne_top
  apply hmul.memLp_map_measure_iff.mpr
  have hcomp : (fun r => V (r / κ)) ∘ (fun r => κ * r) = V := by
    funext r
    change V (κ * r / κ) = V r
    congr 1
    field_simp [hκ]
  rw [hcomp]
  exact hV

/-- The boundary-normalized natural vector is transported by that very
same isometry.  This keeps the supplied natural solution, even when its
value at the matching cut vanishes. -/
theorem inverseRadiusEquiv_symm_normalized_ae
    (hκ : κ ≠ 0) (hβ : 0 < β)
    (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
    {q : Lp ℝ 2 μ} {V : ℝ → ℝ} {lam : ℝ}
    (hq : (q : ℝ → ℝ) =ᵐ[μ] fun r => V r / sqrt lam) :
    ((inverseRadiusEquiv hκ hβ hm).symm q : ℝ → ℝ) =ᵐ[ν]
      fun r => V (r / κ) / sqrt (β * lam) := by
  filter_upwards [inverseRadiusEquiv_symm_ae_of_ae hκ hβ hm hq] with r hr
  rw [hr, radialRadiusScale, sqrt_mul hβ.le]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end ContinuousFlexibility.Radial
