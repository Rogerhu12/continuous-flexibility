import ContinuousFlexibility.Radial.SelectedTailRegularResponse

/-!
# Natural-line uniqueness in the actual radial coordinate

This is the first-order uniqueness already proved by the deep natural
line and the finite core transfer. Its inputs are the actual value and
physical flux, not a postulated separated graph or inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def RadialTailCauchyUnique (D : ReferenceData) (right : Bool)
    (cut J lam : ℝ) (v : ℝ × ℝ) : Prop :=
  ∀ u p : ℝ → ℝ,
    ContinuousOn u (radialTailHalf D right cut) →
    ContinuousOn p (radialTailHalf D right cut) →
    (∀ r ∈ radialTailInterval D right cut,
      HasDerivAt u (p r / D.w r) r ∧
        HasDerivAt p (J * deriv D.w r / r * u r) r) →
    MemLp u 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →
    outerStatePair v (u cut, outerTailSign right * p cut / lam) = 0 →
    ∀ r ∈ radialTailHalf D right cut, u r = 0

theorem radialTailInterval_outward (D : ReferenceData) (right : Bool) (cut r : ℝ) :
    r ∈ radialTailInterval D right cut ↔
      outerOutwardRadius right r ∈ Ioo (outerTailSign right * cut)
        (outerTailSign right * tailPhysicalEndpoint D right) := by
  cases right <;>
    simp [radialTailInterval, outerOutwardRadius, outerTailSign, tailPhysicalEndpoint, and_comm]

theorem OuterWeightedHomogeneousUnique.radial
    {D : ReferenceData} (hD : IsAccumulatingProfile D) {right : Bool} {cut J lam : ℝ}
    {v : ℝ × ℝ} (hcut : cut ∈ radialCore D) (hlam : lam ≠ 0)
    (hunique : OuterWeightedHomogeneousUnique
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut))
      (outerTailOutwardWeight D right) (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right) J lam v) :
    RadialTailCauchyUnique D right cut J lam v := by
  intro u p hu hp hsys hLp hRobin r hr
  let y : ℝ → ℝ := fun x => u (outerOutwardRadius right x)
  let z : ℝ → ℝ := fun x => outerTailSign right * p (outerOutwardRadius right x) / lam
  have hmap : MapsTo (outerOutwardRadius right)
      (Ico (outerTailSign right * cut) (outerTailSign right * tailPhysicalEndpoint D right))
      (radialTailHalf D right cut) := by
    intro x hx
    apply (radialTailHalf_outward D right cut _).mpr
    simpa only [outerOutwardRadius_twice] using hx
  have hyc : ContinuousOn y (Ico (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right)) :=
    hu.comp (contDiff_outerOutwardRadius right).continuous.continuousOn hmap
  have hzc : ContinuousOn z (Ico (outerTailSign right * cut)
      (outerTailSign right * tailPhysicalEndpoint D right)) :=
    (continuousOn_const.mul
      (hp.comp (contDiff_outerOutwardRadius right).continuous.continuousOn hmap)).div_const lam
  have hstate : OuterFirstOrderSystem (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x)) y z
      (Ioo (outerTailSign right * cut) (outerTailSign right * tailPhysicalEndpoint D right)) := by
    intro x hx
    have hxold : outerOutwardRadius right x ∈ radialTailInterval D right cut := by
      apply (radialTailInterval_outward D right cut _).mpr
      simpa only [outerOutwardRadius_twice] using hx
    have hcore := selectedTailInterval_subset_core hcut right hxold
    have hwn := ((matchingProfileGeometry hD).2.2.2.2.1 _ hcore).ne'
    have hxp : 0 < outerOutwardRadius right x := (matchingProfileGeometry hD).1.trans hcore.1
    have hx0 : x ≠ 0 := by
      intro hx0
      simpa [hx0, outerOutwardRadius] using hxp
    have hwderiv : deriv (outerTailOutwardWeight D right) x =
        outerTailSign right * deriv D.w (outerOutwardRadius right x) := by
      unfold outerTailOutwardWeight
      rw [deriv_comp_mul_left]
      simp only [smul_eq_mul, outerOutwardRadius_eq_sign]
    obtain ⟨hd, hdflux⟩ := hsys _ hxold
    constructor
    · apply (hd.comp x (hasDerivAt_outerOutwardRadius right x)).congr_deriv
      dsimp only [z, outerTailOutwardWeight]
      rw [← outerOutwardRadius_eq_sign]
      field_simp [hlam, hwn]
      <;> ring
    · apply (((hdflux.comp x (hasDerivAt_outerOutwardRadius right x)).const_mul
        (outerTailSign right)).div_const lam).congr_deriv
      dsimp only [y]
      rw [hwderiv, outerOutwardRadius_eq_sign]
      cases right <;> simp only [outerTailSign, Bool.false_eq_true, ite_false, ite_true,
        neg_one_mul, one_mul] <;> field_simp [hlam, hx0] <;> ring
  have hyLp : MemLp y 2
      (outerOutwardIntervalMeasure D right (radialTailInterval D right cut)) := by
    rw [outerOutwardRegionMeasure_eq_map hcut]
    apply (measurableEmbedding_outerOutwardRadius right).memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, y, outerOutwardRadius_twice] using hLp
  have hzRobin : outerStatePair v (y (outerTailSign right * cut),
      z (outerTailSign right * cut)) = 0 := by
    simpa only [y, z, outerOutwardRadius_eq_sign, ← mul_assoc,
      outerTailSign_mul_self, one_mul] using hRobin
  have hz := hunique y z hyc hzc hstate hyLp hzRobin
    (outerOutwardRadius right r) ((radialTailHalf_outward D right cut r).mp hr)
  simpa only [y, outerOutwardRadius_twice] using hz.1

theorem RadialTailCauchyUnique.radiusScale
    {D E : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {κ β cut J lam : ℝ} {v : ℝ × ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hcut : cut ∈ radialCore D)
    (hcutE : κ * cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hunique : RadialTailCauchyUnique D right cut J lam v) :
    RadialTailCauchyUnique E right (κ * cut) J (β * lam) v := by
  intro u p hu hp hsys hLp hRobin x hx
  let U : ℝ → ℝ := fun r => u (κ * r)
  let P : ℝ → ℝ := fun r => p (κ * r) / β
  have hmap : MapsTo (fun r : ℝ => κ * r) (radialTailHalf D right cut)
      (radialTailHalf E right (κ * cut)) :=
    fun r hr => (radialTailHalf_radius_mul hκ right hend).mpr hr
  have hU : ContinuousOn U (radialTailHalf D right cut) :=
    hu.comp (continuous_const.mul continuous_id).continuousOn hmap
  have hP : ContinuousOn P (radialTailHalf D right cut) :=
    (hp.comp (continuous_const.mul continuous_id).continuousOn hmap).div_const β
  have hstate : ∀ r ∈ radialTailInterval D right cut,
      HasDerivAt U (P r / D.w r) r ∧
        HasDerivAt P (J * deriv D.w r / r * U r) r := by
    intro r hr
    have hi : κ * r ∈ radialTailInterval E right (κ * cut) := by
      rw [← radialTailInterval_radius_image (entry := cut) hκ right hend]
      exact ⟨r, hr, rfl⟩
    have hrCore := selectedTailInterval_subset_core hcut right hr
    have hr0 := ((matchingProfileGeometry hD).1.trans hrCore.1).ne'
    have hwn := ((matchingProfileGeometry hD).2.2.2.2.1 _ hrCore).ne'
    have hwderiv : deriv E.w (κ * r) = β * deriv D.w r := by
      have hopen : IsOpen (radialTailInterval D right cut) := by cases right <;> exact isOpen_Ioo
      rw [(referenceProfile_radiusScale_eventuallyEq hκ.ne' hopen hr hprofile).deriv_eq,
        deriv_radialRadiusScale_apply_mul hκ.ne']
      field_simp [hκ.ne'] <;> ring
    obtain ⟨hd, hdflux⟩ := hsys _ hi
    have hcoord : HasDerivAt (fun r : ℝ => κ * r) κ r := hasDerivAt_const_mul κ
    constructor
    · apply (hd.comp r hcoord).congr_deriv
      dsimp only [P]
      rw [hprofile r hr]
      field_simp [hκ.ne', hβ.ne', hwn] <;> ring
    · apply ((hdflux.comp r hcoord).div_const β).congr_deriv
      dsimp only [U]
      rw [hwderiv]
      field_simp [hκ.ne', hβ.ne', hr0] <;> ring
  have hUscale : radialRadiusScale κ 1 U = u := by
    funext r
    have hcancel : κ * (r / κ) = r := by field_simp [hκ.ne'] <;> ring
    simp only [radialRadiusScale, U, hcancel, one_mul]
  have hULp : MemLp U 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) := by
    apply (memLp_radialRadiusScale_tail_iff hκ hβ one_ne_zero right hcut hcutE hend hprofile).mp
    rwa [hUscale]
  have hURobin : outerStatePair v (U cut, outerTailSign right * P cut / lam) = 0 := by
    have he : outerTailSign right * P cut / lam =
        outerTailSign right * p (κ * cut) / (β * lam) := by
      dsimp only [P]
      rw [← mul_div_assoc, div_div]
    simpa only [U, he] using hRobin
  have hz := hunique U P hU hP hstate hULp hURobin (x / κ)
    ((radialTailHalf_radius_div hκ right hend).mp hx)
  have hcancel : κ * (x / κ) = x := by field_simp [hκ.ne'] <;> ring
  simpa only [U, hcancel] using hz

end ContinuousFlexibility.Radial
