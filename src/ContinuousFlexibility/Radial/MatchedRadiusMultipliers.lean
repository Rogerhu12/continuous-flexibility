import ContinuousFlexibility.Radial.MatchedRadiusGreenKernel
import ContinuousFlexibility.Analysis.L2BoundedMultiplier

/-!
# Exact multiplier transport by the actual radius isometry

This applies to the final reference localizers pulled back by dilation,
including their finite core where the geometry coordinate need not be
linear. The inverse and the supplied L² vectors are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis

variable {μ ν : Measure ℝ} {κ β : ℝ}
  (hκ : κ ≠ 0) (hβ : 0 < β)
  (hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r))
  {φ ψ : ℝ → ℝ} {M N : ℝ}
  (hφ : AEStronglyMeasurable φ μ) (hψ : AEStronglyMeasurable ψ ν)
  (hφb : ∀ᵐ x ∂μ, |φ x| ≤ M) (hψb : ∀ᵐ x ∂ν, |ψ x| ≤ N)
  (hχ : (fun x => ψ (κ * x)) =ᵐ[μ] φ)

include hχ

theorem inverseRadiusEquiv_multiplier (f : Lp ℝ 2 ν) :
    inverseRadiusEquiv hκ hβ hm (l2BoundedMultiplier ν hψ hψb f) =
      l2BoundedMultiplier μ hφ hφb (inverseRadiusEquiv hκ hβ hm f) := by
  apply Lp.ext
  filter_upwards [
    inverseRadiusEquiv_ae hκ hβ hm (l2BoundedMultiplier ν hψ hψb f),
    (inverseRadius_ae_iff hκ hβ hm).mp (l2BoundedMultiplier_ae ν hψ hψb f),
    l2BoundedMultiplier_ae μ hφ hφb (inverseRadiusEquiv hκ hβ hm f),
    inverseRadiusEquiv_ae hκ hβ hm f, hχ] with x hleft hmul hright hf hlocal
  rw [hleft, hmul, hright, hf, hlocal]
  ring

theorem norm_inverseRadiusEquiv_multiplier (f : Lp ℝ 2 ν) :
    ‖l2BoundedMultiplier ν hψ hψb f‖ =
      ‖l2BoundedMultiplier μ hφ hφb (inverseRadiusEquiv hκ hβ hm f)‖ := by
  rw [← (inverseRadiusEquiv hκ hβ hm).norm_map,
    inverseRadiusEquiv_multiplier hκ hβ hm hφ hψ hφb hψb hχ]

theorem inverseRadiusOperator_multipliers
    {φ' ψ' : ℝ → ℝ} {M' N' : ℝ}
    (hφ' : AEStronglyMeasurable φ' μ) (hψ' : AEStronglyMeasurable ψ' ν)
    (hφb' : ∀ᵐ x ∂μ, |φ' x| ≤ M') (hψb' : ∀ᵐ x ∂ν, |ψ' x| ≤ N')
    (hχ' : (fun x => ψ' (κ * x)) =ᵐ[μ] φ')
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    (l2BoundedMultiplier ν hψ hψb).comp
        ((inverseRadiusOperator hκ hβ hm R).comp (l2BoundedMultiplier ν hψ' hψb')) =
      inverseRadiusOperator hκ hβ hm
        ((l2BoundedMultiplier μ hφ hφb).comp (R.comp (l2BoundedMultiplier μ hφ' hφb'))) := by
  let U := inverseRadiusEquiv hκ hβ hm
  have hleft := inverseRadiusEquiv_multiplier hκ hβ hm hφ hψ hφb hψb hχ
  have hright := inverseRadiusEquiv_multiplier hκ hβ hm hφ' hψ' hφb' hψb' hχ'
  apply ContinuousLinearMap.ext
  intro f
  apply U.injective
  simp only [ContinuousLinearMap.comp_apply, inverseRadiusOperator_apply]
  change U (l2BoundedMultiplier ν hψ hψb
      (U.symm (R (U (l2BoundedMultiplier ν hψ' hψb' f))))) =
    U (U.symm (l2BoundedMultiplier μ hφ hφb
      (R (l2BoundedMultiplier μ hφ' hφb' (U f)))))
  rw [hleft, U.apply_symm_apply, hright, U.apply_symm_apply]

theorem norm_inverseRadiusOperator_multipliers
    {φ' ψ' : ℝ → ℝ} {M' N' : ℝ}
    (hφ' : AEStronglyMeasurable φ' μ) (hψ' : AEStronglyMeasurable ψ' ν)
    (hφb' : ∀ᵐ x ∂μ, |φ' x| ≤ M') (hψb' : ∀ᵐ x ∂ν, |ψ' x| ≤ N')
    (hχ' : (fun x => ψ' (κ * x)) =ᵐ[μ] φ')
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    ‖(l2BoundedMultiplier ν hψ hψb).comp
        ((inverseRadiusOperator hκ hβ hm R).comp (l2BoundedMultiplier ν hψ' hψb'))‖ =
      ‖(l2BoundedMultiplier μ hφ hφb).comp (R.comp (l2BoundedMultiplier μ hφ' hφb'))‖ := by
  rw [inverseRadiusOperator_multipliers hκ hβ hm hφ hψ hφb hψb hχ
    hφ' hψ' hφb' hψb' hχ', norm_inverseRadiusOperator]

end ContinuousFlexibility.Radial
