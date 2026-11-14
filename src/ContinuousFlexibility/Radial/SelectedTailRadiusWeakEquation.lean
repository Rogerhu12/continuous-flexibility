module

public import ContinuousFlexibility.Radial.SelectedTailInverseRadius
public import ContinuousFlexibility.Radial.SelectedTailWeakPairing

/-!
# Weak equations for the same inverse on the actual scaled reference

The operator, Jacobi test source, smooth test and measure all use the
same radius/height transport. The square-root density factors cancel in
the inner products. No equality of entire reference profiles is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem RadialTailWeakPairing.radiusScale
    {D E : ReferenceData} {hD : IsAccumulatingProfile D} {hE : IsAccumulatingProfile E}
    {right : Bool} {κ β cut : ℝ} {j : ℕ}
    (hκ : 0 < κ) (hβ : 0 < β) (hcut : cut ∈ radialCore D)
    (hcutE : κ * cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    {R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))}
    (hR : RadialTailWeakPairing D hD right cut j R) :
    RadialTailWeakPairing E hE right (κ * cut) j
      (inverseRadiusOperator hκ.ne' hβ
        (radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hcut hcutE hend hprofile) R) := by
  let μ := (radialHilbertMeasure D).restrict (radialTailInterval D right cut)
  let ν := (radialHilbertMeasure E).restrict (radialTailInterval E right (κ * cut))
  have hm : ν = ENNReal.ofReal β • μ.map (fun r => κ * r) :=
    radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hcut hcutE hend hprofile
  let T := inverseRadiusEquiv hκ.ne' hβ hm
  have hI : IsOpen (radialTailInterval D right cut) := by cases right <;> exact isOpen_Ioo
  have hIs : MeasurableSet (radialTailInterval D right cut) := hI.measurableSet
  intro ψ hψ hs f
  let φ : ℝ → ℝ := fun r => ψ (κ * r)
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (contDiff_const.mul contDiff_id)
  have hsφ : Function.support φ ⊆ radialTailInterval D right cut := by
    intro r hr
    have himage := radialTailInterval_radius_image (entry := cut) hκ right hend
    have hi : κ * r ∈ (fun t : ℝ => κ * t) '' radialTailInterval D right cut := by
      rw [himage]
      exact hs hr
    obtain ⟨t, ht, he⟩ := hi
    have htr : t = r := mul_left_cancel₀ hκ.ne' he
    simpa only [htr] using ht
  let qD : Lp ℝ 2 μ := l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
    (matchingJacobiVector D hD j φ hφ)
  let pD : Lp ℝ 2 μ := l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut)
    (matchingSmoothVector D hD φ hφ)
  let qE : Lp ℝ 2 ν := l2Restrict (radialHilbertMeasure E) (radialTailInterval E right (κ * cut))
    (matchingJacobiVector E hE j ψ hψ)
  let pE : Lp ℝ 2 ν := l2Restrict (radialHilbertMeasure E) (radialTailInterval E right (κ * cut))
    (matchingSmoothVector E hE ψ hψ)
  have hqD : (qD : ℝ → ℝ) =ᵐ[μ] matchingJacobiTest D j φ :=
    (l2Restrict_coeFn _ _ _).trans (ae_restrict_of_ae (MemLp.coeFn_toLp _))
  have hpD : (pD : ℝ → ℝ) =ᵐ[μ] φ :=
    (l2Restrict_coeFn _ _ _).trans (ae_restrict_of_ae (MemLp.coeFn_toLp _))
  have hqE : (qE : ℝ → ℝ) =ᵐ[ν] matchingJacobiTest E j ψ :=
    (l2Restrict_coeFn _ _ _).trans (ae_restrict_of_ae (MemLp.coeFn_toLp _))
  have hpE : (pE : ℝ → ℝ) =ᵐ[ν] ψ :=
    (l2Restrict_coeFn _ _ _).trans (ae_restrict_of_ae (MemLp.coeFn_toLp _))
  have hq : T qE = sqrt β • qD := by
    apply Lp.ext
    filter_upwards [inverseRadiusEquiv_ae_of_ae hκ.ne' hβ hm hqE,
      Lp.coeFn_smul (sqrt β) qD, hqD, ae_restrict_mem hIs] with r hr hsmul hqr hri
    rw [hr, hsmul, Pi.smul_apply, smul_eq_mul, hqr,
      matchingJacobiTest_radiusScale hκ.ne' hβ.ne' hI hri hprofile]
  have hp : T pE = sqrt β • pD := by
    apply Lp.ext
    filter_upwards [inverseRadiusEquiv_ae_of_ae hκ.ne' hβ hm hpE,
      Lp.coeFn_smul (sqrt β) pD, hpD] with r hr hsmul hpr
    rw [hr, hsmul, Pi.smul_apply, smul_eq_mul, hpr]
  have hold : ⟪R (T f), qD⟫_ℝ = -⟪T f, pD⟫_ℝ := hR φ hφ hsφ (T f)
  change ⟪T.symm (R (T f)), qE⟫_ℝ = -⟪f, pE⟫_ℝ
  rw [← T.inner_map_map (T.symm (R (T f))) qE, T.apply_symm_apply,
    hq, inner_smul_right, hold, ← T.inner_map_map f pE, hp, inner_smul_right]
  ring

end ContinuousFlexibility.Radial
