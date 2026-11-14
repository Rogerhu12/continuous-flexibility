module

public import ContinuousFlexibility.Radial.ConnectedLaterBoundary
public import ContinuousFlexibility.Radial.SelectedOuterPoisson

/-!
# Both later Poisson columns on one actual connected reference

The two dilation witnesses retain their exterior maps. Thus the actual
matching cuts lie on opposite sides of the central patch, which proves
their order. The same natural representatives then produce both actual
Poisson columns, with the physical scales and every frozen exterior trace.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem ConnectedReferenceGeometry.selected_later_cuts_geometry
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes)
    (G : MorseChainGeometryWitness Γ.selected.chain)
    (hentry : Γ.selected.entry = r07CellEntry Γ.selected.chain)
    (hcut : ∀ right n, Γ.selected.chain.index < n →
      Γ.selected.cut right n = r07PreviousCellCut Γ.selected.chain right (n - 1))
    (κ : Bool → ℝ)
    (hmap : ∀ right r,
      r ∈ radialTailInterval (Γ.selected.family Γ.selected.sigma) right
        (Γ.selected.entry right Γ.selected.chain.index) →
      κ right * r ∈ radialTailInterval Γ.reference right
        (if right then Γ.centralRight else Γ.centralLeft))
    {n j : ℕ} (hn : Γ.selected.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand Γ.selected.chain Γ.selected.Cstar n j) :
    let cut := fun right => κ right * Γ.selected.joinInner right n
    Γ.reference.a < cut false ∧ cut false < Γ.centralLeft ∧
      Γ.centralRight < cut true ∧ cut true < Γ.reference.b ∧ cut false < cut true := by
  have hretained (right : Bool) :
      Γ.selected.joinInner right n ∈
        radialTailInterval (Γ.selected.family Γ.selected.sigma) right
          (Γ.selected.entry right Γ.selected.chain.index) := by
    obtain ⟨hp, hsub⟩ := selected_later_span_retained hΓ.1 G hentry right
      hn hj heven hband (hcut right n hn)
    exact hsub hp
  have hL := hmap false _ (hretained false)
  have hR := hmap true _ (hretained true)
  have hpatch := hΓ.2.2.2.2.1
  have hmiddle : Γ.centralLeft < Γ.centralRight :=
    hpatch.2.1.trans (central_turning_radii_pos_ordered.2.trans hpatch.2.2.1)
  exact ⟨hL.1, hL.2, hR.1, hR.2, hL.2.trans (hmiddle.trans hR.1)⟩

theorem ConnectedReferenceGeometry.selected_later_outerPoisson_data
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
    {n j : ℕ} (hn : Γ.selected.chain.index < n) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand Γ.selected.chain Γ.selected.Cstar n j) :
    let S := Γ.selected
    let D := Γ.reference
    ∃ κ β : Bool → ℝ, ∃ v : Bool → ℝ → ℝ,
      (∀ right, 0 < κ right ∧ 0 < β right) ∧
      let cut := fun right => κ right * S.joinInner right n
      let V := fun right => radialRadiusScale (κ right) 1 (v right)
      let lam := fun right => standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut right)) (cut right)
      D.a < cut false ∧ cut false < Γ.centralLeft ∧
      Γ.centralRight < cut true ∧ cut true < D.b ∧ cut false < cut true ∧
      (∀ right,
        ContDiff ℝ ∞ (v right) ∧
        EqOn (v right) (S.outgoing right j)
          (radialTailInterval (S.family S.sigma) right (S.entry right n)) ∧
        v right (S.entry right n) = S.outgoing right j (S.entry right n) ∧
        deriv (v right) (S.entry right n) = deriv (S.outgoing right j) (S.entry right n) ∧
        ContDiff ℝ ∞ (V right) ∧ RadialNaturalTail D right j (cut right) (V right) ∧
        0 < lam right ∧
        selectedBoundaryState D j (r07OutwardSign right) (cut right) (V right) ≠ 0 ∧
        let d := standInBoundarySlope (r07OutwardSign right) ((j : ℝ) ^ 2) (cut right)
          (radialRadiusScale (κ right) 1 (S.incoming right j))
        let AB := outerUnitState
          (selectedBoundaryState D j (r07OutwardSign right) (cut right) (V right))
        0 < d ∧ d ≤ 1 / 2 ∧ AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
        (r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8 ≤ |AB.1 * d - AB.2|) ∧
      ∀ M : RadialMatchingData D, M.frequency = j →
        M.innerLeft = cut false → M.innerRight = cut true →
        (∀ i, M.boundaryScale i = lam (if i = 0 then false else true)) →
        ∃ P : Fin 2 → RadialModePair D, ∃ p : Fin 2 → ℝ → ℝ,
          ∀ i,
            let right := if i = 0 then false else true
            let state := selectedBoundaryState D j (bufferSign i) (cut right) (V right)
            let AB := outerUnitState state
            p i = modeOuterSideFunction M.innerLeft M.innerRight right
              (fun r => V right r / (sqrt (state.1 ^ 2 + state.2 ^ 2) * sqrt (lam right))) ∧
            (((P i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p i) ∧
            (((P i).1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
              (Ioo M.innerLeft M.innerRight)] fun _ => 0) ∧
            (∀ r ∈ Ioo M.innerLeft M.innerRight, p i r = 0) ∧
            ContDiffOn ℝ 2 (p i) (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
            (P i).2 = 0 ∧ ModeLocalEquation D j (matchingOuterRegion D M) (P i) 0 ∧
            AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
            ∀ k, p i (matchingCut D M k) = (if k = i then AB.1 else 0) /
                sqrt (M.boundaryScale k) ∧
              matchingOuterFlux D M (p i) k = (if k = i then AB.2 else 0) := by
  classical
  let S := Γ.selected
  let D := Γ.reference
  choose κ β hκ hβ hmap hdata using
    (fun right => Γ.selected_later_boundary_data_retained hΓ G hC hentry hcut hjoin
      hregular hsmall hselected right)
  choose v hv using (fun right => hdata right n j hn hj heven hband)
  let cut := fun right => κ right * S.joinInner right n
  let V := fun right => radialRadiusScale (κ right) 1 (v right)
  let lam := fun right => standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut right)) (cut right)
  have hgeometry := Γ.selected_later_cuts_geometry hΓ G hentry hcut κ hmap hn hj heven hband
  have hV (right : Bool) : ContDiff ℝ ∞ (V right) :=
    contDiff_const.mul ((hv right).1.comp (contDiff_id.div_const (κ right)))
  have hN (right : Bool) : RadialNaturalTail D right j (cut right) (V right) := by
    rcases hv right with ⟨_, _, _, _, _, _, _, _, hN, _⟩
    exact hN
  have hlam (right : Bool) : 0 < lam right := by
    rcases hv right with ⟨_, _, _, _, _, _, _, _, _, _, hl, _⟩
    exact hl
  have hne (right : Bool) :
      selectedBoundaryState D j (r07OutwardSign right) (cut right) (V right) ≠ 0 := by
    rcases hv right with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hne, _⟩
    exact hne
  refine ⟨κ, β, v, (fun right => ⟨hκ right, hβ right⟩), hgeometry.1,
    hgeometry.2.1, hgeometry.2.2.1, hgeometry.2.2.2.1, hgeometry.2.2.2.2, ?_, ?_⟩
  · intro right
    rcases hv right with
      ⟨hvs, _, hEq, hvalue, hderiv, _, _, _, hnatural, _, hscale, hd₀, hd₁,
        hstate, hunit, hmargin⟩
    exact ⟨hvs, hEq, hvalue, hderiv, hV right, hnatural, hscale, hstate,
      hd₀, hd₁, hunit, hmargin⟩
  · intro M hfreq hleft hright hscale
    have ha : D.a < M.innerLeft := by rw [hleft]; exact hgeometry.1
    have hm : M.innerLeft < M.innerRight := by
      rw [hleft, hright]
      exact hgeometry.2.2.2.2
    have hb : M.innerRight < D.b := by rw [hright]; exact hgeometry.2.2.2.1
    have hcutM (i : Fin 2) : matchingCut Γ.reference M i =
        κ (if i = 0 then false else true) *
          Γ.selected.joinInner (if i = 0 then false else true) n := by
      fin_cases i
      · exact hleft
      · exact hright
    have hindex (i : Fin 2) :
        (if (if i = 0 then false else true) then (1 : Fin 2) else 0) = i := by
      fin_cases i <;> norm_num
    have hsign (i : Fin 2) : bufferSign i =
        r07OutwardSign (if i = 0 then false else true) := by
      fin_cases i <;> norm_num [bufferSign, r07OutwardSign]
    have hpoisson (i : Fin 2) := exists_selectedOuterPoisson hΓ.2.1 M ha hm hb
      (if i = 0 then false else true) (hV _)
      (by rw [hindex, hfreq, hcutM]; exact hN _)
      (by rw [hindex, hscale]; exact hlam _)
      (by rw [hindex, hscale, hfreq, hcutM])
      (by rw [hindex, hfreq, hcutM, hsign]; exact hne _)
    choose P p hp using hpoisson
    refine ⟨P, p, ?_⟩
    intro i
    simpa only [hindex, hfreq, hcutM, hscale] using hp i

end ContinuousFlexibility.Radial
