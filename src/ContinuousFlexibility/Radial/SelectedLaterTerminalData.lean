import ContinuousFlexibility.Blueprint.R10a.Geometry
import ContinuousFlexibility.Radial.SelectedLaterPairBoundary
import ContinuousFlexibility.Radial.SelectedLaterCutoffGeometry
import ContinuousFlexibility.Radial.SelectedTerminalMatching
import ContinuousFlexibility.Radial.SelectedTerminalBudget
import ContinuousFlexibility.Radial.SelectedTerminalInnerSupply
import ContinuousFlexibility.Radial.SelectedRetainedOuterSupply
import ContinuousFlexibility.Radial.TerminalRegionalData

/-!
# Actual later-band regional data on the retained reference

The shell is built from the selected natural solutions at the actual
scaled joins. The stand-ins, cutoff functions and measured errors all
come from the same retained Morse caps. Only the already constructed
regional inverse outputs are passed through supply predicates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.exists_later_terminalData_of_supplies_with_data
    {C : ℝ} {requested : ℕ} {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (metadata : R10aSelectedMetadata C requested S)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hC : 1000 ≤ S.Cstar) {n j : ℕ} (hn : S.chain.index < n)
    (hj : 2 ≤ j) (heven : Even j) (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hbudget : 1000000000 ≤ terminalMatchingAction S.chain (n - 1) j ∧
      (radialE n ^ terminalMorseEnergyErrorExponent + radialE n ^ (38 : ℝ) *
        (radialE n ^ terminalMorseRelativeSourceExponent) ^ (2 : ℕ)) *
        exp (-(terminalMatchingAction S.chain (n - 1) j / 100000000) -
          terminalMatchingAction S.chain (n - 1) j / 100000000) ≤
        ((r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8) / 16)
    (hinner : ∀ (margin : ℝ) (slope : Bool → ℝ) (boundary : Bool → ℝ × ℝ),
      SelectedTerminalInnerSupply
        (selectedTerminalMatching Γ.reference j n margin
          (fun side => P.sideRadius side * S.joinInner side n) slope boundary)
        (radialE n ^ (38 : ℝ))) :
    ∃ W : TerminalRegionalData Γ.reference,
      W.matching.frequency = j ∧ W.matching.transitionIndex = n ∧
      W.matching.innerLeft = P.sideRadius false * S.joinInner false n ∧
      W.matching.innerRight = P.sideRadius true * S.joinInner true n ∧
      W.cutoff = (fun i => P.laterTerminalCutoff metadata.geometry n (selectedTerminalSide i)) ∧
      W.standIn = (fun i => radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
        (S.incoming (selectedTerminalSide i) j)) ∧
      W.matching.margin = r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2) / 8 ∧
      W.sourceCost = radialE n ^ terminalMorseRelativeSourceExponent ∧
      W.energyCost = radialE n ^ terminalMorseEnergyErrorExponent ∧
      W.inverseCost = radialE n ^ (38 : ℝ) ∧
      (∀ i, W.attenuation i = terminalMatchingAction S.chain (n - 1) j / 100000000) ∧
      W.matching.sourceOuter = modeOuterSource Γ.reference
        (P.sideRadius false * S.joinInner false n) (P.sideRadius true * S.joinInner true n) ∧
      ∃ v : Bool → ℝ → ℝ,
        (∀ side, ContDiff ℝ ∞ (v side) ∧
          EqOn (v side) (S.outgoing side j)
            (radialTailInterval (S.family S.sigma) side (S.entry side n)) ∧
          ContDiff ℝ ∞ (radialRadiusScale (P.sideRadius side) 1 (v side)) ∧
          RadialNaturalTail Γ.reference side j (P.sideRadius side * S.joinInner side n)
            (radialRadiusScale (P.sideRadius side) 1 (v side))) ∧
        ∀ i : Fin 2,
          W.matching.A i i =
            (outerUnitState (selectedBoundaryState Γ.reference j
              (r07OutwardSign (selectedTerminalSide i))
              (P.sideRadius (selectedTerminalSide i) * S.joinInner (selectedTerminalSide i) n)
              (radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
                (v (selectedTerminalSide i))))).1 ∧
          W.matching.B i i =
            (outerUnitState (selectedBoundaryState Γ.reference j
              (r07OutwardSign (selectedTerminalSide i))
              (P.sideRadius (selectedTerminalSide i) * S.joinInner (selectedTerminalSide i) n)
              (radialRadiusScale (P.sideRadius (selectedTerminalSide i)) 1
                (v (selectedTerminalSide i))))).2 := by
  let D := Γ.reference
  let G := metadata.geometry
  let cut : Bool → ℝ := fun side => P.sideRadius side * S.joinInner side n
  let U : Bool → ℝ → ℝ := fun side =>
    radialRadiusScale (P.sideRadius side) 1 (S.incoming side j)
  let χ : Bool → ℝ → ℝ := P.laterTerminalCutoff G n
  let margin : ℝ := r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2) / 8
  let attenuation : ℝ := terminalMatchingAction S.chain (n - 1) j / 100000000
  let sourceCost : ℝ := radialE n ^ terminalMorseRelativeSourceExponent
  let energyCost : ℝ := radialE n ^ terminalMorseEnergyErrorExponent
  have hD : RadialProfileGeometry D := (Classical.choose_spec hΓ.2.1).1
  have hincoming (side : Bool) := (metadata.regular side n j hj heven hband).1
  have houtgoing (side : Bool) := (metadata.regular side n j hj heven hband).2
  have hcut (side : Bool) := metadata.later_cut side n hn
  have hjoin (side : Bool) := metadata.later_join side n hn
  have hboundary (side : Bool) := P.selected_later_pair_boundary hD hw metadata.selected G
    metadata.entry metadata.first_two hC metadata.join_small side hn hj heven hband
    (hcut side) (hjoin side) (hincoming side) (houtgoing side)
    (metadata.later_angle side n j hj heven hn hband)
  choose v hv hveq hdata using hboundary
  let V : Bool → ℝ → ℝ := fun side => radialRadiusScale (P.sideRadius side) 1 (v side)
  let slope : Bool → ℝ := fun side =>
    standInBoundarySlope (r07OutwardSign side) ((j : ℝ) ^ 2) (cut side) (U side)
  let boundary : Bool → ℝ × ℝ := fun side =>
    outerUnitState (selectedBoundaryState D j (r07OutwardSign side) (cut side) (V side))
  have hb (side : Bool) : cut side ∈ radialCore D ∧ ContDiff ℝ ∞ (V side) ∧
      RadialNaturalTail D side j (cut side) (V side) ∧ U side (cut side) = 1 ∧
      0 < standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut side)) (cut side) ∧
      0 < slope side ∧ slope side ≤ 1 / 2 ∧
      selectedBoundaryState D j (r07OutwardSign side) (cut side) (V side) ≠ 0 ∧
      (boundary side).1 ^ 2 + (boundary side).2 ^ 2 = 1 ∧
      margin ≤ |(boundary side).1 * slope side - (boundary side).2| := hdata side
  obtain ⟨hcuts, hχsmooth, hχderiv, hχdisjoint, hχcolumn, hχgerm, hUeq, hLayer, _⟩ :=
    P.later_cutoff_geometry metadata.selected G metadata.entry metadata.first_two hC hq
      hΓ hw hleft hright hn hj heven hband hcut hjoin hincoming
  have horder : D.a < cut false ∧ cut false < cut true ∧ cut true < D.b :=
    ⟨(hb false).1.1, hcuts, (hb true).1.2⟩
  have hcolumn : Function.support (referenceColumn D) ⊆ Ioo (cut false) (cut true) := by
    obtain ⟨hLC, hCL, _, hRC, hCJ⟩ :=
      P.later_matching_cap_order metadata.selected G metadata.entry metadata.first_two
        hq hleft hright hn hj heven hband hcut
    intro r hr
    have hc := connectedReference_column_in_central hΓ (subset_tsupport _ hr)
    exact ⟨(hLC.trans hCL).trans hc.1, hc.2.trans (hRC.trans hCJ)⟩
  let M₀ := selectedTerminalMatching D j n margin cut slope boundary
  obtain ⟨A, u, hAnorm, hAsolve, hAunique, hArep⟩ := hinner margin slope boundary
  obtain ⟨R, vouter, Q, p, hR⟩ :=
    P.selectedTerminal_outerSupply hΓ.2.1 hΓ.2.2.1 hw metadata.selected G
      metadata.family_endpoints metadata.entry metadata.first_two metadata.later_cut
      hj heven hband V (fun side => (hb side).2.1) (fun side => (hb side).2.2.1)
      hcuts margin slope A u
  let M : RadialMatchingData D := { M₀ with
    innerInverse := A
    innerRepresentative := u
    outerInverse := R
    outerRepresentative := vouter
    outerPoisson := Q
    outerFunction := p }
  have hMcut (i : Fin 2) : matchingCut D M i = cut (selectedTerminalSide i) :=
    selectedTerminalMatching_cut D j n margin cut slope boundary i
  have hMdiag (i : Fin 2) : M.A i i = (boundary (selectedTerminalSide i)).1 ∧
      M.B i i = (boundary (selectedTerminalSide i)).2 :=
    selectedTerminalMatching_diagonal D j n margin cut slope boundary i
  have hsourceNonneg : 0 ≤ sourceCost :=
    Real.rpow_nonneg (show 0 ≤ radialE n from (exp_pos _).le) _
  have henergyNonneg : 0 ≤ energyCost :=
    Real.rpow_nonneg (show 0 ≤ radialE n from (exp_pos _).le) _
  have hcap (side : Bool) := P.reference_later_cutoff_source_energy hD hw metadata.selected G
    metadata.entry metadata.first_two hC side hn hj heven hband (hcut side) (hjoin side)
    (hincoming side) hbudget.1
  have hsourceBound (side : Bool) :
      (eLpNorm (terminalCapHilbertSource
        (standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut side)) (cut side))
        D.w (χ side) (U side)) 2 (radialHilbertMeasure D)).toReal ≤
        (sourceCost * sqrt (slope side)) * exp (-attenuation) := by
    have hbnonneg : 0 ≤ (sqrt (slope side) * sourceCost) * exp (-attenuation) :=
      mul_nonneg (mul_nonneg (sqrt_nonneg _) hsourceNonneg) (exp_pos _).le
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap side).2.1
    change (eLpNorm (terminalCapHilbertSource
        (standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut side)) (cut side))
        D.w (χ side) (U side)) 2 (radialHilbertMeasure D)).toReal ≤
      (ENNReal.ofReal ((sqrt (slope side) * sourceCost) * exp (-attenuation))).toReal at he
    rw [ENNReal.toReal_ofReal hbnonneg] at he
    convert he using 1 <;> ring
  have henergyBound (side : Bool) :
      |(∫ r in (cut false)..(cut true), terminalCapCutoffEnergy D.w (χ side) (U side) r) /
        standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut side)) (cut side)| ≤
        energyCost * slope side * exp (-2 * attenuation) := by
    obtain ⟨hnonneg, hbound⟩ := (hcap side).2.2 (cut false) (cut true)
      (hLayer side).1 (hLayer side).2
    change (∫ r in (cut false)..(cut true), terminalCapCutoffEnergy D.w (χ side) (U side) r) /
        standInBoundaryScale ((j : ℝ) ^ 2) (D.w (cut side)) (cut side) ≤
      slope side * energyCost * exp (-2 * attenuation) at hbound
    rw [abs_of_nonneg hnonneg]
    simpa only [mul_comm (slope side) energyCost] using hbound
  refine ⟨{
    matching := M
    cut_order := horder
    column_inside := hcolumn
    margin_pos := div_pos
      (mul_pos (r07UniformTolerance_pos metadata.selected.1.le) (exp_pos _)) (by norm_num)
    diagonal := ?_
    boundary_off_diagonal := selectedTerminalMatching_offDiagonal D j n margin cut slope boundary
    boundary_normalized := ?_
    inner_solve := hAsolve
    inner_unique := hAunique
    inner_source := fun _ => rfl
    inner_representative := hArep
    outer := hR
    cutoff := fun i => χ (selectedTerminalSide i)
    standIn := fun i => U (selectedTerminalSide i)
    cutoff_smooth := fun i => hχsmooth (selectedTerminalSide i)
    standIn_smooth := fun i => contDiff_radialRadiusScale (hincoming (selectedTerminalSide i)) _ _
    standIn_equation := fun i => hUeq (selectedTerminalSide i)
    source_memLp := fun i => (hcap (selectedTerminalSide i)).1
    cutoff_derivative_inside := fun i => hχderiv (selectedTerminalSide i)
    cutoff_disjoint := ?_
    cutoff_column_disjoint := fun i => hχcolumn (selectedTerminalSide i)
    cutoff_boundary := ?_
    standIn_boundary := ?_
    boundary_scale := ?_
    frequency_pos := by exact_mod_cast (by omega : 0 < j)
    boundary_slope := ?_
    attenuation := fun _ => attenuation
    sourceCost := sourceCost
    energyCost := energyCost
    inverseCost := radialE n ^ (38 : ℝ)
    sourceCost_nonneg := hsourceNonneg
    energyCost_nonneg := henergyNonneg
    source_bound := fun i => hsourceBound (selectedTerminalSide i)
    energy_bound := fun i => henergyBound (selectedTerminalSide i)
    inverse_bound := hAnorm
    error_budget := fun _ _ => hbudget.2 }, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, (fun _ => rfl), rfl,
    v, (fun side => ⟨hv side, hveq side, (hb side).2.1, (hb side).2.2.1⟩), hMdiag⟩
  · intro i
    rw [(hMdiag i).1, (hMdiag i).2]
    rcases hb (selectedTerminalSide i) with ⟨_, _, _, _, hlam, hdpos, hdhalf, _, _, hmargin⟩
    exact ⟨hlam, hdpos, hdhalf, hmargin⟩
  · intro i
    rw [(hMdiag i).1, (hMdiag i).2]
    exact (hb (selectedTerminalSide i)).2.2.2.2.2.2.2.2.1
  · intro i k hik
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hχdisjoint
    · exact hχdisjoint.symm
    · exact (hik rfl).elim
  · intro i
    rw [hMcut i]
    exact hχgerm (selectedTerminalSide i)
  · intro i
    rw [hMcut i]
    exact (hb (selectedTerminalSide i)).2.2.2.1
  · intro i
    rw [hMcut i]
    rfl
  · intro i
    change standInBoundarySlope (bufferSign i) ((j : ℝ) ^ 2)
      (matchingCut D M i) (U (selectedTerminalSide i)) = slope (selectedTerminalSide i)
    rw [hMcut i, selectedTerminalSide_sign i]

/-- The original interface forgets only the exact cap and natural-line data. -/
theorem SeedRetainedPair.exists_later_terminalData_of_supplies
    {C : ℝ} {requested : ℕ} {S : SelectedTailData}
    {K : SeedCentralCutoff} {q length : ℝ} (P : SeedRetainedPair S K q length)
    (metadata : R10aSelectedMetadata C requested S)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
    (hC : 1000 ≤ S.Cstar) {n j : ℕ} (hn : S.chain.index < n)
    (hj : 2 ≤ j) (heven : Even j) (hband : radialFrequencyBand S.chain S.Cstar n j)
    (hbudget : 1000000000 ≤ terminalMatchingAction S.chain (n - 1) j ∧
      (radialE n ^ terminalMorseEnergyErrorExponent + radialE n ^ (38 : ℝ) *
        (radialE n ^ terminalMorseRelativeSourceExponent) ^ (2 : ℕ)) *
        exp (-(terminalMatchingAction S.chain (n - 1) j / 100000000) -
          terminalMatchingAction S.chain (n - 1) j / 100000000) ≤
        ((r07UniformTolerance S.Cstar * exp (-(n : ℝ) ^ 2)) / 8) / 16)
    (hinner : ∀ (margin : ℝ) (slope : Bool → ℝ) (boundary : Bool → ℝ × ℝ),
      SelectedTerminalInnerSupply
        (selectedTerminalMatching Γ.reference j n margin
          (fun side => P.sideRadius side * S.joinInner side n) slope boundary)
        (radialE n ^ (38 : ℝ))) :
    ∃ W : TerminalRegionalData Γ.reference,
      W.matching.frequency = j ∧ W.matching.transitionIndex = n ∧
      W.matching.innerLeft = P.sideRadius false * S.joinInner false n ∧
      W.matching.innerRight = P.sideRadius true * S.joinInner true n := by
  obtain ⟨W, hfreq, hindex, hcutL, hcutR, _⟩ :=
    P.exists_later_terminalData_of_supplies_with_data metadata hq hΓ hw hleft hright
      hC hn hj heven hband hbudget hinner
  exact ⟨W, hfreq, hindex, hcutL, hcutR⟩

end ContinuousFlexibility.Radial
