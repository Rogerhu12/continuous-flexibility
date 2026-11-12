import ContinuousFlexibility.Radial.SelectedSideTransport
import ContinuousFlexibility.Radial.SelectedLaterRetained
import ContinuousFlexibility.Radial.SelectedLaterStandIn
import ContinuousFlexibility.Radial.SelectedBoundaryRadiusScale

/-!
# Later incoming solutions on the same retained pair

Both endpoint normalizations and the complete homogeneous interval use
the retained pair's actual radius dilation. The derivative sign and the
normalized boundary slope survive this positive dilation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.reference_later_incoming_data {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
    (G : MorseChainGeometryWitness S.chain) (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hC : 1000 ≤ S.Cstar) (right : Bool) {n j : ℕ}
    (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut right n = r07PreviousCellCut S.chain right (n - 1))
    (hjoin : S.joinInner right n = r07PreviousCellJoin S.chain right (n - 1))
    (hu : ContDiff ℝ ∞ (S.incoming right j)) :
    let κ := P.sideRadius right
    let U := radialRadiusScale κ 1 (S.incoming right j)
    ContDiff ℝ ∞ U ∧ U (κ * S.cut right n) = 0 ∧
      U (κ * S.joinInner right n) = 1 ∧
      (if right then 0 < deriv U (κ * S.cut right n)
        else deriv U (κ * S.cut right n) < 0) ∧
      (∀ r ∈ uIcc (κ * S.cut right n) (κ * S.entry right n),
        radialJacobi ((j : ℝ) ^ 2) D.w U r = 0) ∧
      0 < standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
        (κ * S.joinInner right n) U ∧
      standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
        (κ * S.joinInner right n) U ≤ 1 / 2 := by
  let κ := P.sideRadius right
  let U := radialRadiusScale κ 1 (S.incoming right j)
  have hκ : 0 < κ := P.sideRadius_pos right
  have hb := hS.2.2.2.2.2 right n j hj heven hband
  rcases hb with ⟨_, _, _, _, _, _, hinit, _, _, _, hODE, _, _⟩
  have hnorm : S.incoming right j (S.cut right n) = 0 ∧
      S.incoming right j (S.joinInner right n) = 1 ∧
      (if right then 0 < deriv (S.incoming right j) (S.cut right n)
        else deriv (S.incoming right j) (S.cut right n) < 0) := by
    simpa only [if_neg hn.ne'] using hinit
  have hbase := hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hfirst
  have he₀ := hbase.2.1
  have hbaseOrder := hbase.2.2.2.2.1
  have hretained := (selected_later_span_retained hS G hentry right hn hj heven hband hcut).2
  have hstand := selected_later_standIn_bounds hS G hC right hn hj heven hband hcut hjoin hu
  have hslope : 0 < standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
        (κ * S.joinInner right n) U ∧
      standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2)
        (κ * S.joinInner right n) U ≤ 1 / 2 := by
    simpa only [U, standInBoundarySlope_radialRadiusScale_one hκ.ne'] using hstand.2
  refine ⟨contDiff_radialRadiusScale hu κ 1, ?_, ?_, ?_, ?_, hslope⟩
  · change radialRadiusScale κ 1 (S.incoming right j) (κ * S.cut right n) = 0
    rw [radialRadiusScale_apply_mul hκ.ne', one_mul]
    exact hnorm.1
  · change radialRadiusScale κ 1 (S.incoming right j) (κ * S.joinInner right n) = 1
    rw [radialRadiusScale_apply_mul hκ.ne', one_mul]
    exact hnorm.2.1
  · have hd : deriv U (κ * S.cut right n) =
        (1 / κ) * deriv (S.incoming right j) (S.cut right n) :=
      deriv_radialRadiusScale_apply_mul hκ.ne' 1 (S.incoming right j) (S.cut right n)
    rw [hd]
    cases right
    · exact mul_neg_of_pos_of_neg (one_div_pos.mpr hκ) hnorm.2.2
    · exact mul_pos (one_div_pos.mpr hκ) hnorm.2.2
  · intro r hr
    have hx : r / κ ∈ uIcc (S.cut right n) (S.entry right n) :=
      (mem_uIcc_div_pos hκ).mpr hr
    have ht := hretained hx
    have hxcore : r / κ ∈ radialCore (S.family S.sigma) := by
      cases right
      · exact ⟨ht.1, ht.2.trans he₀.2⟩
      · exact ⟨he₀.1.trans ht.1, ht.2⟩
    have hout : if right then S.cut right S.chain.index ≤ r / κ
        else r / κ ≤ S.cut right S.chain.index := by
      cases right
      · exact (ht.2.trans (hbaseOrder.1.trans hbaseOrder.2)).le
      · exact ((hbaseOrder.1.trans hbaseOrder.2).trans ht.1).le
    have hg := P.reference_side_old_germ hw hS right hxcore hout
    have h := radialJacobi_radiusScale_of_profile_germ (α := 1) hκ.ne' hg
      (hODE.2 (r / κ) hx)
    have heq : κ * (r / κ) = r := by field_simp [hκ.ne']
    simpa only [heq] using h

end ContinuousFlexibility.Radial
