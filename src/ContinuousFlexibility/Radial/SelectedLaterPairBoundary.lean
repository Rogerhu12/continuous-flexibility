module

public import ContinuousFlexibility.Radial.SelectedFirstNaturalTransport
public import ContinuousFlexibility.Radial.SelectedLaterPhysicalIncoming
public import ContinuousFlexibility.Radial.SelectedLaterJoinAngle
public import ContinuousFlexibility.Radial.SelectedBoundaryRadiusScale

/-!
# Later boundary data for the retained pair's actual dilation

The selected natural solution is continued once to the actual matching
join. The fixed pair's own radius and height factors transport its state,
so the terminal cap, inner chain and outer Robin condition use the same
two physical cuts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedPair.selected_later_pair_boundary {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    {D : ReferenceData} (hD : RadialProfileGeometry D) (hw : D.w = P.pair.profile)
    (hS : IsSelectedTail S) (G : MorseChainGeometryWitness S.chain)
    (hentry : S.entry = r07CellEntry S.chain)
    (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
    (hC : 1000 ≤ S.Cstar)
    (hsmall : R07JoinActionSmall S.chain S.Cstar (r07UniformTolerance S.Cstar / 100))
    (side : Bool) {n j : ℕ} (hn : S.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hcut : S.cut side n = r07PreviousCellCut S.chain side (n - 1))
    (hjoin : S.joinInner side n = r07PreviousCellJoin S.chain side (n - 1))
    (hu : ContDiff ℝ ∞ (S.incoming side j)) (hv : ContDiff ℝ ∞ (S.outgoing side j))
    (hsep : r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2) ≤
      radialAngleSine
        (radialState (S.family S.sigma) j (S.entry side n)
          ((S.family S.sigma).w (S.joinInner side n)) (S.incoming side j))
        (radialState (S.family S.sigma) j (S.entry side n)
          ((S.family S.sigma).w (S.joinInner side n)) (S.outgoing side j))) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      EqOn v (S.outgoing side j)
        (radialTailInterval (S.family S.sigma) side (S.entry side n)) ∧
      let p := P.sideRadius side * S.joinInner side n
      let U := radialRadiusScale (P.sideRadius side) 1 (S.incoming side j)
      let V := radialRadiusScale (P.sideRadius side) 1 v
      let state := selectedBoundaryState D j (r07OutwardSign side) p V
      let AB := outerUnitState state
      let d := standInBoundarySlope (r07OutwardSign side) ((j : ℝ) ^ 2) p U
      p ∈ radialCore D ∧ ContDiff ℝ ∞ V ∧ RadialNaturalTail D side j p V ∧
        U p = 1 ∧ 0 < standInBoundaryScale ((j : ℝ) ^ 2) (D.w p) p ∧
        0 < d ∧ d ≤ 1 / 2 ∧ state ≠ 0 ∧ AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
        (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8 ≤
          |AB.1 * d - AB.2| := by
  have hc : 0 < r07UniformTolerance S.Cstar := r07UniformTolerance_pos hS.1.le
  have hc₁ : r07UniformTolerance S.Cstar ≤ 1 :=
    (r07UniformTolerance_le S.Cstar).trans (by norm_num)
  obtain ⟨v, hvs, hNv, _, _, hEq, _, _, _, hangle⟩ :=
    selected_later_natural_join_angle hS G hc hc₁ hsmall side hn hj heven hband hjoin hu hv hsep
  have hstand := selected_later_standIn_bounds hS G hC side hn hj heven hband hcut hjoin hu
  have hp := (hS.2.2.2.2.2 side n j hj heven hband).2.2.1
  have hret := (selected_later_cut_join_entry_retained hS G hentry side
    hn hj heven hband hcut).2.1
  have ho := (hS.2.2.2.2.2 side S.chain.index 2 le_rfl (by decide) hfirst).2.2.2.2.1
  have hout : if side then S.cut side S.chain.index ≤ S.joinInner side n
      else S.joinInner side n ≤ S.cut side S.chain.index := by
    cases side
    · exact (hret.2.trans (ho.1.trans ho.2)).le
    · exact ((ho.1.trans ho.2).trans hret.1).le
  obtain ⟨hpD, hprofile, hN⟩ := P.reference_natural_tail_transport hD hw hS side hp hout hNv
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hε : r07OutwardSign side = 1 ∨ r07OutwardSign side = -1 := by
    cases side
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 < (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 2 := by positivity
  have hangle' : (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 2 ≤
      radialAngleSine
        (radialState (S.family S.sigma) j (S.joinInner side n)
          ((S.family S.sigma).w (S.joinInner side n)) v)
        (radialState (S.family S.sigma) j (S.joinInner side n)
          ((S.family S.sigma).w (S.joinInner side n)) (S.incoming side j)) := by
    rw [radialAngleSine_comm]
    exact hangle
  obtain ⟨hU, hlam, hd₀, hd₁, hne, hunit, hmargin⟩ :=
    selectedBoundaryRadiusScale_data (D := S.family S.sigma) (E := D)
      (P.sideRadius_pos side).ne' (P.sideHeight_pos side).ne' hjpos.ne'
      (hD.1.trans hpD.1) (hD.2.2.2.2.1 _ hpD) hε hprofile
      hstand.1 hstand.2 hδ hangle'
  refine ⟨v, hvs, hEq, hpD, contDiff_radialRadiusScale hvs _ _, hN,
    hU, hlam, hd₀, hd₁, hne, hunit, ?_⟩
  convert hmargin using 1 <;> ring

end ContinuousFlexibility.Radial
