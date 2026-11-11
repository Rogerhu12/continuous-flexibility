import ContinuousFlexibility.Radial.SelectedSideTransport
import ContinuousFlexibility.Radial.SelectedNaturalJoin
import ContinuousFlexibility.Radial.SelectedNaturalTailTransport

/-!
# The first-band natural solution on the same retained reference

The original selected outgoing solution is continued to its actual join,
with its complete old tail and entrance jet unchanged. The retained pair's
proved profile germs and actual endpoints then transport this very solution
to the common reference. No new selected tail or natural line is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem selectedBoundaryState_ne_zero_of_natural {D : ReferenceData}
    (hD : RadialProfileGeometry D) {right : Bool} {j : ℕ} {r ε : ℝ}
    (hj : (j : ℝ) ≠ 0) (hr : r ∈ radialCore D) (hε : ε ≠ 0)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hN : RadialNaturalTail D right j r v) :
    selectedBoundaryState D j ε r v ≠ 0 := by
  have hw : D.w r ≠ 0 := (hD.2.2.2.2.1 r hr).ne'
  have hlam : standInBoundaryScale ((j : ℝ) ^ 2) (D.w r) r ≠ 0 :=
    (standInBoundaryScale_pos (sq_pos_of_ne_zero hj)
      (hD.2.2.2.2.1 r hr) (hD.1.trans hr.1)).ne'
  intro hz
  have hvalue : v r = 0 := congrArg Prod.fst hz
  have hflux : ε * D.w r * deriv v r /
      standInBoundaryScale ((j : ℝ) ^ 2) (D.w r) r = 0 := congrArg Prod.snd hz
  have hmul : ε * D.w r * deriv v r = 0 :=
    (div_eq_zero_iff.mp hflux).resolve_right hlam
  have hderiv : deriv v r = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hε hw)
  exact radialNaturalTail_cauchyData_ne_zero hD hr hv hN (Prod.ext hvalue hderiv)

/-- Any genuine natural entrance outside the original first cut is retained
by the same actual pair, with the proved target endpoints and L2 measure. -/
theorem SeedRetainedPair.reference_natural_tail_transport {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {E : ReferenceData} (hE : RadialProfileGeometry E) (hw : E.w = P.pair.profile)
    (hS : IsSelectedTail S) (right : Bool) {j : ℕ} {entry : ℝ}
    (hentry : entry ∈ radialCore (S.family S.sigma))
    (hout : if right then S.cut right S.chain.index ≤ entry
      else entry ≤ S.cut right S.chain.index)
    {v : ℝ → ℝ} (hN : RadialNaturalTail (S.family S.sigma) right j entry v) :
    P.sideRadius right * entry ∈ radialCore E ∧
      E.w (P.sideRadius right * entry) =
        (P.sideHeight right * P.sideRadius right) * (S.family S.sigma).w entry ∧
      RadialNaturalTail E right j (P.sideRadius right * entry)
        (radialRadiusScale (P.sideRadius right) 1 v) := by
  let D := S.family S.sigma
  have hreal : MorseChainRealization S.chain S.sigma D S.constants :=
    (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hD : RadialProfileGeometry D := hreal.geometry
  have hκ := P.sideRadius_pos right
  have hβ := P.sideHeight_pos right
  have hvalue := P.reference_side_old_value hw hS right hentry hout
  have htarget : P.sideRadius right * entry ∈ radialCore E := by
    apply radialCore_mem_of_profile_pos hE
    rw [hvalue]
    exact mul_pos (mul_pos hβ hκ) (hD.2.2.2.2.1 entry hentry)
  have hprofile (r : ℝ) (hr : r ∈ radialTailInterval D right entry) :
      E.w (P.sideRadius right * r) =
        (P.sideHeight right * P.sideRadius right) * D.w r := by
    have hrCore : r ∈ radialCore D := by
      cases right
      · exact ⟨hr.1, hr.2.trans hentry.2⟩
      · exact ⟨hentry.1.trans hr.1, hr.2⟩
    have hrOut : if right then S.cut right S.chain.index ≤ r
        else r ≤ S.cut right S.chain.index := by
      cases right
      · exact hr.2.le.trans hout
      · exact hout.trans hr.1.le
    exact P.reference_side_old_value hw hS right hrCore hrOut
  exact ⟨htarget, hvalue,
    radialNaturalTail_reference_scaled hκ hβ one_ne_zero right hentry htarget
      (P.reference_side_endpoint hE hw right) hprofile hN⟩

/-- The first band's natural representative at its original join, now on
the same common reference. Its full physical state is nonzero even when
the natural function's value at that join is zero. -/
theorem SeedRetainedPair.selected_first_natural_data {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {E : ReferenceData} (hE : RadialProfileGeometry E) (hw : E.w = P.pair.profile)
    (hS : IsSelectedTail S) (right : Bool) {j : ℕ} (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index j)
    (hv : ContDiff ℝ ∞ (S.outgoing right j)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      RadialNaturalTail (S.family S.sigma) right j (S.joinInner right S.chain.index) v ∧
      EqOn v (S.outgoing right j)
        (radialTailInterval (S.family S.sigma) right (S.entry right S.chain.index)) ∧
      v (S.entry right S.chain.index) = S.outgoing right j (S.entry right S.chain.index) ∧
      deriv v (S.entry right S.chain.index) =
        deriv (S.outgoing right j) (S.entry right S.chain.index) ∧
      let c := P.sideRadius right * S.joinInner right S.chain.index
      let V := radialRadiusScale (P.sideRadius right) 1 v
      c ∈ radialCore E ∧ ContDiff ℝ ∞ V ∧ RadialNaturalTail E right j c V ∧
      0 < standInBoundaryScale ((j : ℝ) ^ 2) (E.w c) c ∧
      selectedBoundaryState E j (r07OutwardSign right) c V ≠ 0 ∧
      (outerUnitState (selectedBoundaryState E j (r07OutwardSign right) c V)).1 ^ 2 +
        (outerUnitState (selectedBoundaryState E j (r07OutwardSign right) c V)).2 ^ 2 = 1 := by
  obtain ⟨v, hvs, hNv, hvalue, hderiv, hEq, _, _, _⟩ :=
    selected_natural_continue_to_join hS right hj heven hband hv
  have hdata := hS.2.2.2.2.2 right S.chain.index j hj heven hband
  obtain ⟨_, _, hp, _, horder, _, _, _, _, _, _, _, _⟩ := hdata
  have hout : if right then S.cut right S.chain.index ≤ S.joinInner right S.chain.index
      else S.joinInner right S.chain.index ≤ S.cut right S.chain.index := by
    cases right
    · exact horder.2.le
    · exact horder.1.le
  obtain ⟨hc, _, hN⟩ := P.reference_natural_tail_transport hE hw hS right hp hout hNv
  have hV := contDiff_radialRadiusScale hvs (P.sideRadius right) 1
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hε : r07OutwardSign right ≠ 0 := by cases right <;> norm_num [r07OutwardSign]
  have hne := selectedBoundaryState_ne_zero_of_natural hE hjn hc hε hV hN
  exact ⟨v, hvs, hNv, hEq, hvalue, hderiv, hc, hV, hN,
    standInBoundaryScale_pos (sq_pos_of_ne_zero hjn) (hE.2.2.2.2.1 _ hc)
      (hE.1.trans hc.1), hne, outerUnitState_unit hne⟩

end ContinuousFlexibility.Radial
