import ContinuousFlexibility.Radial.MatchedOuterRadiusState
import ContinuousFlexibility.Radial.OuterPhysicalFundamentalPair
import ContinuousFlexibility.Radial.SelectedTailRegularResponse

/-!
# The actual physical fundamental pair under retained radius scaling

The profile identity is only assumed on the retained open tail and at its
regular cut. Equality of one-sided derivatives supplies the coefficient
identity at the cut as well. The same four state functions, entrance
direction and continuation coefficients are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem referenceProfile_radiusScale_half
    {D E : ReferenceData} {right : Bool} {κ β cut : ℝ}
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hcut : E.w (κ * cut) = (β * κ) * D.w cut) :
    ∀ r ∈ radialTailHalf D right cut, E.w (κ * r) = (β * κ) * D.w r := by
  intro r hr
  cases right with
  | false =>
      change D.a < r ∧ r ≤ cut at hr
      rcases lt_or_eq_of_le hr.2 with hlt | heq
      · exact hprofile r ⟨hr.1, hlt⟩
      · simpa only [heq] using hcut
  | true =>
      change cut ≤ r ∧ r < D.b at hr
      rcases lt_or_eq_of_le hr.1 with hlt | heq
      · exact hprofile r ⟨hlt, hr.2⟩
      · simpa only [← heq] using hcut

private theorem matchedOuter_scaled_mem {κ a b x : ℝ} (hκ : 0 < κ)
    (hx : x ∈ Ico (κ * a) (κ * b)) : x / κ ∈ Ico a b := by
  constructor
  · exact (le_div_iff₀ hκ).mpr (by simpa only [mul_comm a κ] using hx.1)
  · exact (div_lt_iff₀ hκ).mpr (by simpa only [mul_comm b κ] using hx.2)

theorem outerWhole_profile_radiusScale
    {D E : ReferenceData} {right : Bool} {κ β cut : ℝ}
    (hκ : 0 < κ)
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut) :
    ∀ x ∈ Ico (κ * outerOutwardRadius right cut)
      (κ * outerOutwardRadius right (tailPhysicalEndpoint D right)),
      outerTailOutwardWeight E right x =
        (β * κ) * outerTailOutwardWeight D right (x / κ) := by
  intro x hx
  have hmem := matchedOuter_scaled_mem hκ hx
  have hr : outerOutwardRadius right (x / κ) ∈ radialTailHalf D right cut := by
    apply (radialTailHalf_outward D right cut _).mpr
    simpa only [outerOutwardRadius_twice, outerOutwardRadius_eq_sign] using hmem
  have h := referenceProfile_radiusScale_half hprofile hprofileCut _ hr
  have hc : κ * outerOutwardRadius right (x / κ) = outerOutwardRadius right x := by
    rw [outerOutwardRadius_eq_sign, outerOutwardRadius_eq_sign]
    field_simp [hκ.ne']
    <;> ring
  simp only [outerTailOutwardWeight, ← outerOutwardRadius_eq_sign]
  rw [← hc]
  exact h

theorem outerWhole_profile_deriv_radiusScale
    {D E : ReferenceData} {right : Bool} {κ β cut : ℝ}
    (hD : IsAccumulatingProfile D) (hE : IsAccumulatingProfile E)
    (hκ : 0 < κ)
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut) :
    ∀ x ∈ Ico (κ * outerOutwardRadius right cut)
      (κ * outerOutwardRadius right (tailPhysicalEndpoint D right)),
      deriv (outerTailOutwardWeight E right) x =
        β * deriv (outerTailOutwardWeight D right) (x / κ) := by
  have hw := (outerWhole_weight_smooth (matchingProfileGeometry hD) right).differentiable
    (by simp)
  have hW := (outerWhole_weight_smooth (matchingProfileGeometry hE) right).differentiable
    (by simp)
  have heq := outerWhole_profile_radiusScale hκ hprofile hprofileCut
  intro x hx
  have hd : HasDerivAt
      (fun y => (β * κ) * outerTailOutwardWeight D right (y / κ))
      ((β * κ) * (deriv (outerTailOutwardWeight D right) (x / κ) * (1 / κ))) x :=
    (((hw (x / κ)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const κ)).const_mul (β * κ))
  have he := derivWithin_congr heq (heq x hx)
  rw [(hW x).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ico _ _ x hx),
    hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ico _ _ x hx)] at he
  calc
    _ = (β * κ) * (deriv (outerTailOutwardWeight D right) (x / κ) * (1 / κ)) := he
    _ = _ := by field_simp [hκ.ne']; ring

/-- The supplied pair, with the target's actual physical coefficients and
endpoints. This definition does not assert that the target is a Morse
realization or choose any new natural solution. -/
def OuterFundamentalStatePair.physicalRadiusScale
    {D E : ReferenceData} {right : Bool} {κ β cut deep lam J : ℝ}
    {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right cut) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hD : IsAccumulatingProfile D) (hE : IsAccumulatingProfile E)
    (hκ : 0 < κ) (hβ : 0 < β) (hlam : lam ≠ 0) (hcut : cut ∈ radialCore D)
    (hend : tailPhysicalEndpoint E right = κ * tailPhysicalEndpoint D right)
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut) :
    OuterFundamentalStatePair
      (fun x => (β * lam) / outerTailOutwardWeight E right x)
      (fun x => J * deriv (outerTailOutwardWeight E right) x / ((β * lam) * x))
      (fun x => P (x / κ)) (fun x => ZP (x / κ))
      (fun x => Q (x / κ)) (fun x => ZQ (x / κ))
      (outerOutwardRadius right (κ * cut)) (outerOutwardRadius right (κ * deep))
      (outerOutwardRadius right (tailPhysicalEndpoint E right)) := by
  let R := H.radiusScale_of_profile hκ hβ.ne' hlam
    (outerWhole_profile_radiusScale hκ hprofile hprofileCut)
    (outerWhole_profile_deriv_radiusScale hD hE hκ hprofile hprofileCut)
    (fun x hx => by
      have hn := outerWhole_coordinate_ne_zero (matchingProfileGeometry hD) hcut
        (matchedOuter_scaled_mem hκ hx)
      intro hz
      exact hn (by simp only [hz, zero_div]))
    (fun x hx => (outerWhole_weight_pos (matchingProfileGeometry hD) hcut
      (matchedOuter_scaled_mem hκ hx)).ne')
  have hc : κ * outerOutwardRadius right cut = outerOutwardRadius right (κ * cut) := by
    simp only [outerOutwardRadius_eq_sign]
    ring
  have hd : κ * outerOutwardRadius right deep = outerOutwardRadius right (κ * deep) := by
    simp only [outerOutwardRadius_eq_sign]
    ring
  have hb : κ * outerOutwardRadius right (tailPhysicalEndpoint D right) =
      outerOutwardRadius right (tailPhysicalEndpoint E right) := by
    rw [hend]
    simp only [outerOutwardRadius_eq_sign]
    ring
  refine {
    U := R.U, ZU := R.ZU, V := R.V, ZV := R.ZV
    entrance := R.entrance, scale := R.scale, tailA := R.tailA, tailB := R.tailB
    unit := R.unit, scale_pos := R.scale_pos
    U_initial := ?_, V_initial := ?_, U_system := ?_, V_system := ?_
    U_tail := ?_, ZU_tail := ?_, V_tail := ?_, ZV_tail := ?_, determinant := ?_ }
  · simpa only [hc] using R.U_initial
  · simpa only [hc] using R.V_initial
  · simpa only [hc, hb] using R.U_system
  · simpa only [hc, hb] using R.V_system
  · simpa only [hd, hb] using R.U_tail
  · simpa only [hd, hb] using R.ZU_tail
  · simpa only [hd, hb] using R.V_tail
  · simpa only [hd, hb] using R.ZV_tail
  · simpa only [hc, hb] using R.determinant

theorem OuterFundamentalStatePair.physicalRadiusScale_fields
    {D E : ReferenceData} {right : Bool} {κ β cut deep lam J : ℝ}
    {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => J * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right cut) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hD : IsAccumulatingProfile D) (hE : IsAccumulatingProfile E)
    (hκ : 0 < κ) (hβ : 0 < β) (hlam : lam ≠ 0) (hcut : cut ∈ radialCore D)
    (hend : tailPhysicalEndpoint E right = κ * tailPhysicalEndpoint D right)
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut) :
    let R := H.physicalRadiusScale hD hE hκ hβ hlam hcut hend hprofile hprofileCut
    R.U = (fun x => H.U (x / κ)) ∧ R.ZU = (fun x => H.ZU (x / κ)) ∧
      R.V = (fun x => H.V (x / κ)) ∧ R.ZV = (fun x => H.ZV (x / κ)) ∧
      R.entrance = H.entrance := ⟨rfl, rfl, rfl, rfl, rfl⟩

end ContinuousFlexibility.Radial
