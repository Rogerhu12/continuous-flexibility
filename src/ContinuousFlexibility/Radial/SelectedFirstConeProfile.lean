import ContinuousFlexibility.Radial.FirstConePhysicalIncoming

/-!
# One physical cone coefficient from the retained point to the first join

The old cone and its retained extension agree at the original cut, so
their coefficients are equal. The resulting profile germ holds on the
entire physical cap and gives the actual boundary normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.reference_first_cone_germ {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (right : Bool)
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => C * t))
    {r : ℝ} (hr : r ∈ uIcc (P.sideRadius right * (P.side right).inner)
      (P.sideRadius right * S.joinInner right S.chain.index)) :
    D.w =ᶠ[𝓝 r] fun t => (P.sideHeight right * (P.side right).coneScale) * t := by
  have hκ := P.sideRadius_pos right
  have hm := hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband
  have hc := hm.1
  have hp := hm.2.2.1
  have horder := hm.2.2.2.2.1
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hcpos : 0 < S.cut right S.chain.index := hD₀.1.trans hc.1
  have hppos : 0 < S.joinInner right S.chain.index := hD₀.1.trans hp.1
  let x := r / P.sideRadius right
  have hx : x ∈ uIcc (P.side right).inner (S.joinInner right S.chain.index) :=
    (mem_uIcc_div_pos hκ).mpr hr
  have hxpos : 0 < x := (lt_min (P.side right).inner_pos hppos).trans_le hx.1
  have hscale : P.sideRadius right * x = r := by
    dsimp only [x]
    field_simp [hκ.ne']
  have hnew (hxc : x ∈ uIcc (P.side right).inner (S.cut right S.chain.index)) :
      D.w =ᶠ[𝓝 (P.sideRadius right * x)]
        fun t => (P.sideHeight right * (P.side right).coneScale) * t := by
    cases right
    · exact P.reference_left_cone_germ hw hxpos hxc
    · exact P.reference_right_cone_germ hw hxc
  have hold (hxc : x ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index))
      (ho : if right then S.cut right S.chain.index ≤ x else x ≤ S.cut right S.chain.index) :
      D.w =ᶠ[𝓝 (P.sideRadius right * x)]
        fun t => (P.sideHeight right * (P.side right).coneScale) * t := by
    obtain ⟨C, _, hC⟩ := hcone
    have hCeq : C = (P.side right).coneScale :=
      mul_right_cancel₀ hcpos.ne'
        ((hC _ left_mem_uIcc).eq_of_nhds.symm.trans (P.side right).old_cone_germ.eq_of_nhds)
    have hxcore : x ∈ radialCore (S.family S.sigma) :=
      ⟨(lt_min hc.1 hp.1).trans_le hxc.1, hxc.2.trans_lt (max_lt hc.2 hp.2)⟩
    have hg := (P.reference_side_old_germ hw hS right hxcore ho).trans
      (radialRadiusScale_cone_germ hκ.ne' (hC _ hxc))
    simpa only [hCeq] using hg
  rw [← hscale]
  cases right
  · have hpi : S.joinInner false S.chain.index < (P.side false).inner :=
      horder.2.trans (P.side false).inner_order
    rw [uIcc_of_ge hpi.le] at hx
    by_cases hxc : S.cut false S.chain.index ≤ x
    · apply hnew
      rw [uIcc_of_ge (P.side false).inner_order.le]
      exact ⟨hxc, hx.2⟩
    · apply hold _ (le_of_not_ge hxc)
      rw [uIcc_of_ge horder.2.le]
      exact ⟨hx.1, (le_of_not_ge hxc)⟩
  · have hip : (P.side true).inner < S.joinInner true S.chain.index :=
      (P.side true).inner_order.trans horder.1
    rw [uIcc_of_le hip.le] at hx
    by_cases hxc : x ≤ S.cut true S.chain.index
    · apply hnew
      rw [uIcc_of_le (P.side true).inner_order.le]
      exact ⟨hx.1, hxc⟩
    · apply hold _ (le_of_not_ge hxc)
      rw [uIcc_of_le horder.1.le]
      exact ⟨le_of_not_ge hxc, hx.2⟩

theorem SeedRetainedPair.reference_first_boundaryScale {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (right : Bool)
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ uIcc (S.cut right S.chain.index)
      (S.joinInner right S.chain.index), (S.family S.sigma).w =ᶠ[𝓝 x] (fun t => C * t))
    (j : ℕ) :
    standInBoundaryScale ((j : ℝ) ^ 2)
      (D.w (P.sideRadius right * S.joinInner right S.chain.index))
      (P.sideRadius right * S.joinInner right S.chain.index) =
        (j : ℝ) ^ 2 * (P.sideHeight right * (P.side right).coneScale) := by
  have hp := (hS.2.2.2.2.2 right S.chain.index 2 le_rfl (by decide) hband).2.2.1
  have hD₀ : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hpos : 0 < P.sideRadius right * S.joinInner right S.chain.index :=
    mul_pos (P.sideRadius_pos right) (hD₀.1.trans hp.1)
  have hg := P.reference_first_cone_germ hw hS hband right hcone right_mem_uIcc
  rw [standInBoundaryScale, hg.eq_of_nhds]
  field_simp [hpos.ne'] <;> ring

end ContinuousFlexibility.Radial
