module

public import ContinuousFlexibility.Radial.SelectedRetainedRegionalInverse
public import ContinuousFlexibility.Blueprint.R10a.Geometry

/-!
# The actual retained cut, scale and profile law

The assertions here are consequences of the original selected geometry
and retained profile. They contain no operator or norm assumption and
apply to the finite first band as well as every later band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.selectedOuter_actual_scaling
    {S : SelectedTailData} {K₀ : SeedCentralCutoff} {q length Cstar : ℝ} {requested : ℕ}
    (P : SeedRetainedPair S K₀ q length) (metadata : R10aSelectedMetadata Cstar requested S)
    {E : ReferenceData} (hE : IsAccumulatingProfile E) (hw : E.w = P.pair.profile)
    {n j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j) (right : Bool) :
    let D := S.family S.sigma
    let cut := S.joinInner right n
    let κ := P.sideRadius right
    let β := P.sideHeight right
    let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w cut) cut
    cut ∈ radialCore D ∧ κ * cut ∈ radialCore E ∧ 0 < lam ∧
      tailPhysicalEndpoint E right = κ * tailPhysicalEndpoint D right ∧
      (∀ r ∈ radialTailInterval D right cut, E.w (κ * r) = (β * κ) * D.w r) ∧
      E.w (κ * cut) = (β * κ) * D.w cut ∧
      standInBoundaryScale ((j : ℝ) ^ 2) (E.w (κ * cut)) (κ * cut) = β * lam := by
  let D := S.family S.sigma
  let cut := S.joinInner right n
  let κ := P.sideRadius right
  let β := P.sideHeight right
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (D.w cut) cut
  have hS := metadata.selected
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hD : IsAccumulatingProfile D := ⟨S.constants, hreal.accumulating⟩
  have hp : cut ∈ radialCore D := (hS.2.2.2.2.2 right n j hj heven hband).2.2.1
  have hκ : 0 < κ := P.sideRadius_pos right
  have hβ : 0 < β := P.sideHeight_pos right
  have hout := selected_join_outside_first_cut hS metadata.geometry metadata.entry
    metadata.first_two metadata.later_cut hj heven hband right
  have hvalue : E.w (κ * cut) = (β * κ) * D.w cut :=
    P.reference_side_old_value hw hS right hp hout
  have hpE : κ * cut ∈ radialCore E := by
    apply radialCore_mem_of_profile_pos (matchingProfileGeometry hE)
    rw [hvalue]
    exact mul_pos (mul_pos hβ hκ) ((matchingProfileGeometry hD).2.2.2.2.1 _ hp)
  have hprofile (r : ℝ) (hr : r ∈ radialTailInterval D right cut) :
      E.w (κ * r) = (β * κ) * D.w r := by
    apply P.reference_side_old_value hw hS right (selectedTailInterval_subset_core hp right hr)
    cases right
    · exact hr.2.le.trans hout
    · exact hout.trans hr.1.le
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hlam : 0 < lam := standInBoundaryScale_pos (sq_pos_of_ne_zero hjn)
    ((matchingProfileGeometry hD).2.2.2.2.1 _ hp) ((matchingProfileGeometry hD).1.trans hp.1)
  refine ⟨hp, hpE, hlam, P.reference_side_endpoint (matchingProfileGeometry hE) hw right,
    hprofile, hvalue, ?_⟩
  rw [standInBoundaryScale, hvalue]
  have hκne : P.sideRadius right ≠ 0 := hκ.ne'
  have hcutne : S.joinInner right n ≠ 0 :=
    ((matchingProfileGeometry hD).1.trans hp.1).ne'
  dsimp only [lam, standInBoundaryScale, D, cut, κ, β]
  field_simp [hκne, hcutne]
  <;> ring

end ContinuousFlexibility.Radial
