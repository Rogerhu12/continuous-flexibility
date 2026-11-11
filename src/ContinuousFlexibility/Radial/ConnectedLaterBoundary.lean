import ContinuousFlexibility.Radial.ConnectedLaterTransport
import ContinuousFlexibility.Radial.SelectedLaterJoinAngle
import ContinuousFlexibility.Radial.SelectedLaterStandIn
import ContinuousFlexibility.Radial.SelectedBoundaryRadiusScale

/-!
# Normalized later-band boundary data on the same connected geometry

The actual matching radius is the dilated joinInner of the selected band.
The selected incoming solution itself supplies the stand-in. The natural
solution is continued to that join while preserving its complete old tail.
One dilation from the same connected witness transports both functions.
The full natural state gives unit coefficients and the diagonal margin.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem ConnectedReferenceGeometry.selected_later_boundary_data_retained
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes)
    (G : MorseChainGeometryWitness Γ.selected.chain)
    (hC : 1000 ≤ Γ.selected.Cstar)
    (hentry : Γ.selected.entry = r07CellEntry Γ.selected.chain)
    (hcut : ∀ right n, Γ.selected.chain.index < n →
      Γ.selected.cut right n = r07PreviousCellCut Γ.selected.chain right (n - 1))
    (hjoin : ∀ right n, Γ.selected.chain.index < n →
      Γ.selected.joinInner right n = r07PreviousCellJoin Γ.selected.chain right (n - 1))
    (hregular : ∀ right n j, 2 ≤ j → Even j →
      radialFrequencyBand Γ.selected.chain Γ.selected.Cstar n j →
      ContDiff ℝ ∞ (Γ.selected.incoming right j) ∧
        ContDiff ℝ ∞ (Γ.selected.outgoing right j))
    (hsmall : R07JoinActionSmall Γ.selected.chain Γ.selected.Cstar
      (r07UniformTolerance Γ.selected.Cstar / 100))
    (hselected : ∀ right n j, 2 ≤ j → Even j → Γ.selected.chain.index < n →
      radialFrequencyBand Γ.selected.chain Γ.selected.Cstar n j →
      r07UniformTolerance Γ.selected.Cstar * exp (-(n : ℝ) ^ 2) ≤
        radialAngleSine
          (radialState (Γ.selected.family Γ.selected.sigma) j (Γ.selected.entry right n)
            ((Γ.selected.family Γ.selected.sigma).w (Γ.selected.joinInner right n))
            (Γ.selected.incoming right j))
          (radialState (Γ.selected.family Γ.selected.sigma) j (Γ.selected.entry right n)
            ((Γ.selected.family Γ.selected.sigma).w (Γ.selected.joinInner right n))
            (Γ.selected.outgoing right j)))
    (right : Bool) :
    let S := Γ.selected
    let D := S.family S.sigma
    let E := Γ.reference
    ∃ κ β : ℝ, 0 < κ ∧ 0 < β ∧
      (∀ r ∈ radialTailInterval D right (S.entry right S.chain.index),
        κ * r ∈ radialTailInterval E right
          (if right then Γ.centralRight else Γ.centralLeft)) ∧
      ∀ n j, S.chain.index < n → 2 ≤ j → Even j →
        radialFrequencyBand S.chain S.Cstar n j →
        ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
          RadialNaturalTail D right j (S.joinInner right n) v ∧
          EqOn v (S.outgoing right j) (radialTailInterval D right (S.entry right n)) ∧
          v (S.entry right n) = S.outgoing right j (S.entry right n) ∧
          deriv v (S.entry right n) = deriv (S.outgoing right j) (S.entry right n) ∧
          let p := S.joinInner right n
          let r := κ * p
          let U := radialRadiusScale κ 1 (S.incoming right j)
          let V := radialRadiusScale κ 1 v
          let d := standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2) r U
          let AB := outerUnitState (selectedBoundaryState E j (r07OutwardSign right) r V)
          r ∈ radialCore E ∧ E.w r = (β * κ) * D.w p ∧
          RadialHomogeneousOn E j
            (uIcc (κ * S.cut right n) (κ * S.entry right n)) U ∧
          RadialNaturalTail E right j r V ∧
          U r = 1 ∧ 0 < standInBoundaryScale ((j : ℝ) ^ 2) (E.w r) r ∧
          0 < d ∧ d ≤ 1 / 2 ∧ selectedBoundaryState E j (r07OutwardSign right) r V ≠ 0 ∧
          AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
          (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8 ≤
            |AB.1 * d - AB.2| := by
  let S := Γ.selected
  let D := S.family S.sigma
  let E := Γ.reference
  have hS : IsSelectedTail S := hΓ.1
  have hgeomE : RadialProfileGeometry E := hΓ.2.1.choose_spec.1
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hinitial : S.entry right S.chain.index ∈ radialCore D := by
    rw [hentry]
    exact r10a_actual_entry_mem_core hreal right le_rfl
  obtain ⟨κ, β, α, hκ, hβ, _, _, hmap, htransport⟩ :=
    Γ.selected_natural_tail_transport_retained hΓ right
  let I := radialTailInterval D right (S.entry right S.chain.index)
  have hopen : IsOpen I := by cases right <;> exact isOpen_Ioo
  have hprofile (r : ℝ) (hr : r ∈ I) : E.w (κ * r) = (β * κ) * D.w r := by
    have hrCore : r ∈ radialCore D := by
      cases right
      · exact ⟨hr.1, hr.2.trans hinitial.2⟩
      · exact ⟨hinitial.1.trans hr.1, hr.2⟩
    have hretained : if right then S.entry right S.chain.index ≤ r
        else r ≤ S.entry right S.chain.index := by
      cases right
      · exact hr.2.le
      · exact hr.1.le
    exact (htransport r hrCore hretained).2.1
  have hc₀ : 0 < r07UniformTolerance S.Cstar := r07UniformTolerance_pos hS.1.le
  have hc₀1 : r07UniformTolerance S.Cstar ≤ 1 :=
    (r07UniformTolerance_le S.Cstar).trans (by norm_num)
  refine ⟨κ, β, hκ, hβ, hmap, ?_⟩
  intro n j hn hj heven hband
  have hreg := hregular right n j hj heven hband
  obtain ⟨v, hvs, hNv, hvalue, hderiv, hEq, _, _, _, hangle⟩ :=
    selected_later_natural_join_angle hS G hc₀ hc₀1 hsmall right hn hj heven hband
      (hjoin right n hn) hreg.1 hreg.2 (hselected right n j hj heven hn hband)
  have hstand := selected_later_standIn_bounds hS G hC right hn hj heven hband
    (hcut right n hn) (hjoin right n hn) hreg.1
  have hb := hS.2.2.2.2.2 right n j hj heven hband
  rcases hb with ⟨_, _, hp, _, _, _, _, _, _, _, hODE, _, _⟩
  obtain ⟨hpSpan, hsub⟩ := selected_later_span_retained hS G hentry right
    hn hj heven hband (hcut right n hn)
  have hpRet := hsub hpSpan
  have hpOut : if right then S.entry right S.chain.index ≤ S.joinInner right n
      else S.joinInner right n ≤ S.entry right S.chain.index := by
    cases right
    · exact hpRet.2.le
    · exact hpRet.1.le
  have hpoint := htransport (S.joinInner right n) hp hpOut
  have hNscaled := hpoint.2.2.2.2 j v 1 one_ne_zero hNv
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hε : r07OutwardSign right = 1 ∨ r07OutwardSign right = -1 := by
    cases right
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 < (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 2 :=
    div_pos (mul_pos hc₀ (exp_pos _)) (by norm_num)
  have hsep : (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 2 ≤
      radialAngleSine
        (radialState D j (S.joinInner right n) (D.w (S.joinInner right n)) v)
        (radialState D j (S.joinInner right n) (D.w (S.joinInner right n)) (S.incoming right j)) := by
    rw [radialAngleSine_comm]
    exact hangle
  have hnormalized := selectedBoundaryRadiusScale_data (D := D) (E := E)
    hκ.ne' hβ.ne' hjpos.ne' (hgeomE.1.trans hpoint.1.1)
    (hgeomE.2.2.2.2.1 _ hpoint.1) hε hpoint.2.1 hstand.1 hstand.2 hδ hsep
  rcases hnormalized with ⟨hU, hlam, hd₀, hd₁, hne, hunit, hmargin⟩
  refine ⟨v, hvs, hNv, hEq, hvalue, hderiv, hpoint.1, hpoint.2.1,
    radialHomogeneousOn_reference_scaled_uIcc hκ hopen hsub hprofile hODE 1,
    hNscaled, hU, hlam, hd₀, hd₁, hne, hunit, ?_⟩
  convert hmargin using 1 <;> ring

/-- The original interface retains its complete boundary bundle. -/
theorem ConnectedReferenceGeometry.selected_later_boundary_data
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes)
    (G : MorseChainGeometryWitness Γ.selected.chain)
    (hC : 1000 ≤ Γ.selected.Cstar)
    (hentry : Γ.selected.entry = r07CellEntry Γ.selected.chain)
    (hcut : ∀ right n, Γ.selected.chain.index < n →
      Γ.selected.cut right n = r07PreviousCellCut Γ.selected.chain right (n - 1))
    (hjoin : ∀ right n, Γ.selected.chain.index < n →
      Γ.selected.joinInner right n = r07PreviousCellJoin Γ.selected.chain right (n - 1))
    (hregular : ∀ right n j, 2 ≤ j → Even j →
      radialFrequencyBand Γ.selected.chain Γ.selected.Cstar n j →
      ContDiff ℝ ∞ (Γ.selected.incoming right j) ∧
        ContDiff ℝ ∞ (Γ.selected.outgoing right j))
    (hsmall : R07JoinActionSmall Γ.selected.chain Γ.selected.Cstar
      (r07UniformTolerance Γ.selected.Cstar / 100))
    (hselected : ∀ right n j, 2 ≤ j → Even j → Γ.selected.chain.index < n →
      radialFrequencyBand Γ.selected.chain Γ.selected.Cstar n j →
      r07UniformTolerance Γ.selected.Cstar * exp (-(n : ℝ) ^ 2) ≤
        radialAngleSine
          (radialState (Γ.selected.family Γ.selected.sigma) j (Γ.selected.entry right n)
            ((Γ.selected.family Γ.selected.sigma).w (Γ.selected.joinInner right n))
            (Γ.selected.incoming right j))
          (radialState (Γ.selected.family Γ.selected.sigma) j (Γ.selected.entry right n)
            ((Γ.selected.family Γ.selected.sigma).w (Γ.selected.joinInner right n))
            (Γ.selected.outgoing right j)))
    (right : Bool) :
    let S := Γ.selected
    let D := S.family S.sigma
    let E := Γ.reference
    ∃ κ β : ℝ, 0 < κ ∧ 0 < β ∧
      ∀ n j, S.chain.index < n → 2 ≤ j → Even j →
        radialFrequencyBand S.chain S.Cstar n j →
        ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
          RadialNaturalTail D right j (S.joinInner right n) v ∧
          EqOn v (S.outgoing right j) (radialTailInterval D right (S.entry right n)) ∧
          v (S.entry right n) = S.outgoing right j (S.entry right n) ∧
          deriv v (S.entry right n) = deriv (S.outgoing right j) (S.entry right n) ∧
          let p := S.joinInner right n
          let r := κ * p
          let U := radialRadiusScale κ 1 (S.incoming right j)
          let V := radialRadiusScale κ 1 v
          let d := standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2) r U
          let AB := outerUnitState (selectedBoundaryState E j (r07OutwardSign right) r V)
          r ∈ radialCore E ∧ E.w r = (β * κ) * D.w p ∧
          RadialHomogeneousOn E j
            (uIcc (κ * S.cut right n) (κ * S.entry right n)) U ∧
          RadialNaturalTail E right j r V ∧
          U r = 1 ∧ 0 < standInBoundaryScale ((j : ℝ) ^ 2) (E.w r) r ∧
          0 < d ∧ d ≤ 1 / 2 ∧ selectedBoundaryState E j (r07OutwardSign right) r V ≠ 0 ∧
          AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
          (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8 ≤
            |AB.1 * d - AB.2| := by
  obtain ⟨κ, β, hκ, hβ, _, hdata⟩ :=
    Γ.selected_later_boundary_data_retained hΓ G hC hentry hcut hjoin
      hregular hsmall hselected right
  exact ⟨κ, β, hκ, hβ, hdata⟩

end ContinuousFlexibility.Radial
