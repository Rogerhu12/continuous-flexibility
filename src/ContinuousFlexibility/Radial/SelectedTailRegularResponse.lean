import ContinuousFlexibility.Radial.SelectedRadialOuterInverse
import ContinuousFlexibility.Radial.SelectedTailInverseRadius
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# The actual half-closed exterior representative and its Robin trace

The physical endpoint stays open. Only the regular matching cut is
included. Reflection and the actual radius/height dilation preserve the
one-sided derivative used in the frozen matching graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def radialTailHalf (D : ReferenceData) (right : Bool) (cut : ℝ) : Set ℝ :=
  if right then Ico cut D.b else Ioc D.a cut

theorem radialTailHalf_uniqueDiff (D : ReferenceData) (right : Bool) (cut : ℝ) :
    UniqueDiffOn ℝ (radialTailHalf D right cut) := by
  cases right
  · exact uniqueDiffOn_Ioc _ _
  · exact uniqueDiffOn_Ico _ _

theorem radialTailHalf_cut {D : ReferenceData} {right : Bool} {cut : ℝ}
    (hcut : cut ∈ radialCore D) : cut ∈ radialTailHalf D right cut := by
  cases right
  · exact ⟨hcut.1, le_rfl⟩
  · exact ⟨le_rfl, hcut.2⟩

theorem radialTailInterval_subset_half (D : ReferenceData) (right : Bool) (cut : ℝ) :
    radialTailInterval D right cut ⊆ radialTailHalf D right cut := by
  cases right
  · exact Ioo_subset_Ioc_self
  · exact Ioo_subset_Ico_self

theorem radialTailHalf_outward (D : ReferenceData) (right : Bool) (cut r : ℝ) :
    r ∈ radialTailHalf D right cut ↔
      outerOutwardRadius right r ∈ Ico (outerTailSign right * cut)
        (outerTailSign right * tailPhysicalEndpoint D right) := by
  cases right <;>
    simp [radialTailHalf, outerOutwardRadius, outerTailSign, tailPhysicalEndpoint, and_comm]

theorem hasDerivAt_outerOutwardRadius (right : Bool) (r : ℝ) :
    HasDerivAt (outerOutwardRadius right) (outerTailSign right) r := by
  have hfun : outerOutwardRadius right = (fun y : ℝ => outerTailSign right * y) := by
    funext y
    exact outerOutwardRadius_eq_sign right y
  rw [hfun]
  simpa only [id_eq, mul_one] using
    (hasDerivAt_id r).const_mul (outerTailSign right)

def RadialTailRegularResponse (D : ReferenceData) (right : Bool)
    (cut lam : ℝ) (v : ℝ × ℝ)
    (R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))) : Prop :=
  ∀ f, ∃ u : ℝ → ℝ,
    (R f : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (radialTailInterval D right cut)] u ∧
    ContDiffOn ℝ 1 u (radialTailHalf D right cut) ∧
    outerStatePair v (u cut,
      outerTailSign right * D.w cut * derivWithin u (radialTailHalf D right cut) cut / lam) = 0

theorem OuterWeightedGreenResponse.radial_regular
    {D : ReferenceData} {right : Bool} {cut lam J : ℝ} {v : ℝ × ℝ}
    (hcut : cut ∈ radialCore D)
    {R : Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))}
    (hR : OuterWeightedGreenResponse
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))
      (outerTailOutwardWeight D right) (selectedOutwardDensity D right)
      (outerTailSign right * cut) (outerTailSign right * tailPhysicalEndpoint D right)
      J lam v R) :
    RadialTailRegularResponse D right cut lam v (outerRadialRegionOperator hcut R) := by
  intro f
  obtain ⟨u, p, he, hu, _, _, hflux, _, hRobin⟩ := hR ((outerRegionEquiv hcut).symm f)
  let U : ℝ → ℝ := fun r => u (outerOutwardRadius right r)
  have hmap : MapsTo (outerOutwardRadius right) (radialTailHalf D right cut)
      (Ico (outerTailSign right * cut)
        (outerTailSign right * tailPhysicalEndpoint D right)) :=
    fun r hr => (radialTailHalf_outward D right cut r).mp hr
  have hc := hmap (radialTailHalf_cut hcut)
  have hd : derivWithin U (radialTailHalf D right cut) cut =
      derivWithin u (Ico (outerTailSign right * cut)
        (outerTailSign right * tailPhysicalEndpoint D right)) (outerOutwardRadius right cut) *
          outerTailSign right := by
    exact ((hu.differentiableOn (by norm_num) _ hc).hasDerivWithinAt.comp cut
      (hasDerivAt_outerOutwardRadius right cut).hasDerivWithinAt hmap).derivWithin
        ((radialTailHalf_uniqueDiff D right cut).uniqueDiffWithinAt (radialTailHalf_cut hcut))
  have hflux' : outerTailSign right * D.w cut *
      derivWithin U (radialTailHalf D right cut) cut = p (outerOutwardRadius right cut) := by
    rw [hd]
    calc
      _ = D.w cut * derivWithin u (Ico (outerTailSign right * cut)
          (outerTailSign right * tailPhysicalEndpoint D right)) (outerOutwardRadius right cut) *
            (outerTailSign right * outerTailSign right) := by ring
      _ = _ := by
        rw [outerTailSign_mul_self, mul_one]
        have hp := hflux _ hc
        simpa only [outerTailOutwardWeight, outerOutwardRadius_eq_sign,
          ← mul_assoc, outerTailSign_mul_self, one_mul] using hp.symm
  have hrad : ContDiff ℝ 1 (outerOutwardRadius right) :=
    (contDiff_outerOutwardRadius right).of_le (by simp)
  refine ⟨U, outerRegionEquiv_ae_of_ae hcut he,
    hu.comp hrad.contDiffOn hmap, ?_⟩
  rw [hflux']
  simpa only [U, outerOutwardRadius_eq_sign] using hRobin

theorem radialTailHalf_radius_mul {D E : ReferenceData} {κ cut r : ℝ}
    (hκ : 0 < κ) (right : Bool)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a)) :
    κ * r ∈ radialTailHalf E right (κ * cut) ↔ r ∈ radialTailHalf D right cut := by
  cases right
  · change E.a = κ * D.a at hend
    simp only [radialTailHalf, Bool.false_eq_true, ite_false, mem_Ioc, hend,
      mul_lt_mul_iff_right₀ hκ, mul_le_mul_iff_right₀ hκ]
  · change E.b = κ * D.b at hend
    simp only [radialTailHalf, ite_true, mem_Ico, hend,
      mul_lt_mul_iff_right₀ hκ, mul_le_mul_iff_right₀ hκ]

theorem radialTailHalf_radius_div {D E : ReferenceData} {κ cut r : ℝ}
    (hκ : 0 < κ) (right : Bool)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a)) :
    r ∈ radialTailHalf E right (κ * cut) ↔ r / κ ∈ radialTailHalf D right cut := by
  have hcancel : κ * (r / κ) = r := by field_simp [hκ.ne'] <;> ring
  simpa only [hcancel] using radialTailHalf_radius_mul (r := r / κ) hκ right hend

theorem derivWithin_radialRadiusScale {s t : Set ℝ} {u : ℝ → ℝ}
    {κ α r : ℝ} (hκ : κ ≠ 0)
    (hu : DifferentiableWithinAt ℝ u s r)
    (hmap : MapsTo (fun x : ℝ => x / κ) t s)
    (ht : UniqueDiffWithinAt ℝ t (κ * r)) :
    derivWithin (radialRadiusScale κ α u) t (κ * r) =
      α / κ * derivWithin u s r := by
  have hcancel : κ * r / κ = r := by field_simp [hκ] <;> ring
  have hu' : HasDerivWithinAt u (derivWithin u s r) s (κ * r / κ) := by
    simpa only [hcancel] using hu.hasDerivWithinAt
  have hd := ((hu'.comp (κ * r)
    ((hasDerivAt_id (κ * r)).div_const κ).hasDerivWithinAt hmap).const_mul α).derivWithin ht
  change derivWithin (fun x : ℝ => α * u (x / κ)) t (κ * r) =
    α / κ * derivWithin u s r
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, mul_one,
    mul_assoc, mul_comm, mul_left_comm] using hd

theorem RadialTailRegularResponse.radiusScale
    {D E : ReferenceData} {right : Bool} {κ β cut lam : ℝ} {v : ℝ × ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hcut : cut ∈ radialCore D)
    (hcutE : κ * cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut)
    {R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))}
    (hR : RadialTailRegularResponse D right cut lam v R) :
    RadialTailRegularResponse E right (κ * cut) (β * lam) v
      (inverseRadiusOperator hκ.ne' hβ
        (radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hcut hcutE hend hprofile) R) := by
  let hm := radialHilbertMeasure_restrict_tail_radiusScale hκ hβ right hcut hcutE hend hprofile
  intro f
  obtain ⟨u, he, hu, hRobin⟩ := hR (inverseRadiusEquiv hκ.ne' hβ hm f)
  let α := 1 / sqrt β
  have hmap : MapsTo (fun x : ℝ => x / κ) (radialTailHalf E right (κ * cut))
      (radialTailHalf D right cut) := fun r hr => (radialTailHalf_radius_div hκ right hend).mp hr
  have hd := derivWithin_radialRadiusScale (α := α) hκ.ne'
    (hu.differentiableOn (by norm_num) _ (radialTailHalf_cut hcut)) hmap
    ((radialTailHalf_uniqueDiff E right (κ * cut)).uniqueDiffWithinAt (radialTailHalf_cut hcutE))
  refine ⟨radialRadiusScale κ α u, inverseRadiusEquiv_symm_ae_of_ae hκ.ne' hβ hm he,
    contDiffOn_const.mul (hu.comp (contDiff_id.div_const κ).contDiffOn hmap), ?_⟩
  rw [radialRadiusScale_apply_mul hκ.ne', hd, hprofileCut]
  have hflux : outerTailSign right * ((β * κ) * D.w cut) *
      (α / κ * derivWithin u (radialTailHalf D right cut) cut) / (β * lam) =
        α * (outerTailSign right * D.w cut *
          derivWithin u (radialTailHalf D right cut) cut / lam) := by
    have hn : outerTailSign right * ((β * κ) * D.w cut) *
        (α / κ * derivWithin u (radialTailHalf D right cut) cut) =
        β * (α * (outerTailSign right * D.w cut *
          derivWithin u (radialTailHalf D right cut) cut)) := by
      field_simp [hκ.ne'] <;> ring
    rw [hn, mul_div_mul_left _ _ hβ.ne']
    ring
  rw [hflux]
  calc
    _ = α * outerStatePair v (u cut, outerTailSign right * D.w cut *
        derivWithin u (radialTailHalf D right cut) cut / lam) := by
      simp only [outerStatePair]
      ring
    _ = 0 := by rw [hRobin, mul_zero]

end ContinuousFlexibility.Radial
