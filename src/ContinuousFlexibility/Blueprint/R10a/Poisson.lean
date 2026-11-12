import ContinuousFlexibility.Radial.TerminalRegionalData

/-!
# R10a: the actual terminal Poisson correction

The regional data supply actual cutoffs, stand-ins and inverse operators.
The Hilbert cutoff columns, corrected Poisson representatives and their
flux matrix are constructed here on the same reference and same cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem R10aPoisson {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) (W : TerminalRegionalData D) :
    ∃ M : RadialMatchingData D,
      M.frequency = W.matching.frequency ∧ MatchedPieces D M := by
  classical
  let M := W.matching
  have hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D := by
    intro r hr
    exact ⟨W.cut_order.1.trans_le hr.1, hr.2.trans_lt W.cut_order.2.2⟩
  obtain ⟨L, F, ell, _, _, _, hL, hlrep, hell, houtside, hLscalar, hFscalar,
      hFfix, horth, hltrace, hflux, hpair, hsource⟩ :=
    terminalActualCutoff_columns_exists hD M W.cut_order.2.1 hsub
      W.cutoff W.standIn W.cutoff_smooth W.standIn_smooth W.standIn_equation
      W.source_memLp W.cutoff_derivative_inside W.cutoff_disjoint W.cutoff_column_disjoint
      W.cutoff_boundary W.standIn_boundary W.boundary_scale W.frequency_pos
      (fun i => (W.sourceCost * sqrt (M.D0 i)) * exp (-W.attenuation i)) W.source_bound
  have hG (i : Fin 2) : ModeInnerDirichletGraph D M (M.innerInverse (F i)) (F i) := by
    have hfix : M.sourceInner (F i) = F i :=
      (W.inner_source (F i)).trans (hFfix i)
    have h := W.inner_solve (F i) (fun _ => hFscalar i)
    change ModeInnerDirichletGraph D M
      (M.innerInverse (M.sourceInner (F i))) (M.sourceInner (F i)) at h
    rwa [hfix] at h
  have hflux' (i k : Fin 2) :
      matchingInnerFlux D M (ell k) i = if i = k then M.D0 i else 0 := by
    have hslope : terminalCutoffSlope M W.standIn i = M.D0 i := W.boundary_slope i
    simpa only [hslope] using hflux i k
  obtain ⟨P, p, Db, _, _, hcolumns, hsym, herror⟩ :=
    terminalInnerPoisson_columns_exists hD hB M W.cut_order.2.1 hsub W.column_inside
      L F ell M.D0 (terminalCutoffEnergy M W.cutoff W.standIn) W.attenuation
      W.sourceCost W.energyCost W.inverseCost (M.margin / 16)
      hL hG hlrep hell houtside hLscalar hFscalar hFfix horth hltrace hflux' hpair
      (fun i => (W.diagonal i).2.1.le) W.sourceCost_nonneg W.energyCost_nonneg
      hsource W.energy_bound W.inverse_bound W.error_budget
  let M' : RadialMatchingData D :=
    { M with innerPoisson := P, innerFunction := p, Db := Db }
  have hsourceSpec (F : RadialModePair D) :
      (M'.sourceInner F).2 = F.2 ∧
        ((M'.sourceInner F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
          (fun r => if r ∈ Ioo M'.innerLeft M'.innerRight then F.1 r else 0) := by
    change (M.sourceInner F).2 = F.2 ∧
      ((M.sourceInner F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        (fun r => if r ∈ Ioo M.innerLeft M.innerRight then F.1 r else 0)
    rw [W.inner_source F]
    exact ⟨(modeRegionSources_spec D M.innerLeft M.innerRight F).1,
      (modeRegionSources_spec D M.innerLeft M.innerRight F).2.2.1⟩
  have hinner : MatchingInnerRealizations D M' :=
    matchingInnerRealizations_of_terminal_columns M' W.inner_solve W.inner_unique
      hsourceSpec W.inner_representative P p Db hcolumns rfl rfl rfl
  have houter : MatchingOuterRealizations D M' := W.outer
  have herr (i k : Fin 2) : |M'.Db i k - (if i = k then M'.D0 i else 0)| ≤
      M'.margin / 16 := by
    have hs (i : Fin 2) : sqrt (M.D0 i) ≤ 1 := by
      apply (sqrt_le_iff).mpr
      exact ⟨by norm_num, by nlinarith only [(W.diagonal i).2.2.1]⟩
    have heps : 0 ≤ M.margin / 16 := div_nonneg W.margin_pos.le (by norm_num)
    calc
      _ ≤ (M.margin / 16) * sqrt (M.D0 i) * sqrt (M.D0 k) := herror i k
      _ ≤ (M.margin / 16) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hs i) heps) (hs k)
          (sqrt_nonneg _) (mul_nonneg heps (by norm_num))
      _ = M'.margin / 16 := by ring
  exact ⟨M', rfl, matchedPieces_of_regions W.cut_order W.column_inside W.margin_pos
    W.diagonal herr hinner houter hsym W.boundary_off_diagonal W.boundary_normalized⟩

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R10aPoisson
