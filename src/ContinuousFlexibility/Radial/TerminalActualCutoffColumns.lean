import ContinuousFlexibility.Radial.TerminalCapRegionalLift
import ContinuousFlexibility.Radial.TerminalLiftBoundaryTrace
import ContinuousFlexibility.Radial.TerminalModeLiftPairing

/-!
# Actual cutoff columns for the common inner Poisson construction

Both the growing cone and Morse stand-ins enter through their actual
cutoff, homogeneous solution, source norm and support geometry.  The
Hilbert vectors, retained representatives, diagonal fluxes and source
pairings are constructed here rather than supplied as inverse data.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem terminalCapInnerSource_ae {D : ReferenceData} {l h lam : ℝ}
    {χ u : ℝ → ℝ}
    (hf : MemLp (terminalCapHilbertSource lam D.w χ u) 2 (radialHilbertMeasure D))
    (hs : tsupport (deriv χ) ⊆ Ioo l h) :
    ((terminalCapInnerSource l h lam χ u hf).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      terminalCapHilbertSource lam D.w χ u := by
  let f := terminalCapHilbertSource lam D.w χ u
  have hsupp : Function.support f ⊆ Ioo l h :=
    (terminalCapHilbertSource_support lam D.w χ u).trans hs
  change ((modeInnerSource D l h (hf.toLp f, 0)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] f
  filter_upwards [(modeRegionSources_spec D l h (hf.toLp f, 0)).2.2.1,
    MemLp.coeFn_toLp hf] with r hr hrep
  by_cases hi : r ∈ Ioo l h
  · rw [hr, if_pos hi, hrep]
  · have hz : f r = 0 := by
      by_contra hn
      exact hi (hsupp hn)
    rw [hr, if_neg hi, hz]

theorem terminalCapInnerSource_norm_le_eLpNorm {D : ReferenceData}
    (l h lam : ℝ) (χ u : ℝ → ℝ)
    (hf : MemLp (terminalCapHilbertSource lam D.w χ u) 2 (radialHilbertMeasure D)) :
    ‖terminalCapInnerSource l h lam χ u hf‖ ≤
      (eLpNorm (terminalCapHilbertSource lam D.w χ u) 2 (radialHilbertMeasure D)).toReal := by
  have hn := terminalCapInnerSource_norm_le l h lam χ u hf
  rw [Lp.norm_toLp _ hf] at hn
  calc
    _ = ‖(terminalCapInnerSource l h lam χ u hf).1‖ := by
      rw [Prod.norm_def]
      change max ‖(terminalCapInnerSource l h lam χ u hf).1‖ ‖(0 : ℝ)‖ = _
      rw [norm_zero, max_eq_left (norm_nonneg _)]
    _ ≤ _ := hn

def terminalCutoffSlope {D : ReferenceData} (M : RadialMatchingData D)
    (u : Fin 2 → ℝ → ℝ) (i : Fin 2) : ℝ :=
  standInBoundarySlope (bufferSign i) ((M.frequency : ℝ) ^ 2) (matchingCut D M i) (u i)

def terminalCutoffEnergy {D : ReferenceData} (M : RadialMatchingData D)
    (χ u : Fin 2 → ℝ → ℝ) (i : Fin 2) : ℝ :=
  (∫ r in M.innerLeft..M.innerRight, terminalCapCutoffEnergy D.w (χ i) (u i) r) /
    M.boundaryScale i

/-- All hypotheses about the preliminary columns in
`terminalInnerPoisson_columns_exists`, obtained from the actual two
cutoffs.  The first three clauses identify the constructed objects. -/
theorem terminalActualCutoff_columns_exists {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (M : RadialMatchingData D)
    (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (χ u : Fin 2 → ℝ → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (heq : ∀ i r, r ∈ Ioo M.innerLeft M.innerRight → r ∈ Function.support (χ i) →
      radialJacobi ((M.frequency : ℝ) ^ 2) D.w (u i) r = 0)
    (hf : ∀ i, MemLp (terminalCapHilbertSource (M.boundaryScale i) D.w (χ i) (u i))
      2 (radialHilbertMeasure D))
    (hderiv : ∀ i, tsupport (deriv (χ i)) ⊆ Ioo M.innerLeft M.innerRight)
    (hsep : ∀ i k, i ≠ k → Disjoint (tsupport (χ i)) (tsupport (χ k)))
    (hcolumn : ∀ i, Disjoint (tsupport (referenceColumn D)) (tsupport (χ i)))
    (hown : ∀ i, χ i =ᶠ[𝓝 (matchingCut D M i)] fun _ => (1 : ℝ))
    (hvalue : ∀ i, u i (matchingCut D M i) = 1)
    (hscale : ∀ i, M.boundaryScale i = standInBoundaryScale ((M.frequency : ℝ) ^ 2)
      (D.w (matchingCut D M i)) (matchingCut D M i))
    (hfreq : (0 : ℝ) < M.frequency)
    (sourceBound : Fin 2 → ℝ)
    (hsource : ∀ i, (eLpNorm
      (terminalCapHilbertSource (M.boundaryScale i) D.w (χ i) (u i))
      2 (radialHilbertMeasure D)).toReal ≤ sourceBound i) :
    ∃ (L F : Fin 2 → RadialModePair D) (ell : Fin 2 → ℝ → ℝ),
      (∀ i, L i = terminalCapInnerLift hD M.innerLeft M.innerRight
        (M.boundaryScale i) (hχ i) (hu i)) ∧
      (∀ i, F i = terminalCapInnerSource M.innerLeft M.innerRight
        (M.boundaryScale i) (χ i) (u i) (hf i)) ∧
      (∀ i, ell i = modeInnerExtension M.innerLeft M.innerRight
        (terminalCapLift (M.boundaryScale i) (χ i) (u i))) ∧
      (∀ i, ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (L i) (F i)) ∧
      (∀ i, ((L i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell i) ∧
      (∀ i, ContDiffOn ℝ 1 (ell i) (Icc M.innerLeft M.innerRight)) ∧
      (∀ i r, r ∈ matchingOuterRegion D M → ell i r = 0) ∧
      (∀ i, (L i).2 = 0) ∧ (∀ i, (F i).2 = 0) ∧
      (∀ i, modeInnerSource D M.innerLeft M.innerRight (F i) = F i) ∧
      (∀ i r, r ∈ Icc M.innerLeft M.innerRight → referenceColumn D r * ell i r = 0) ∧
      (∀ i k, ell i (matchingCut D M k) =
        (if i = k then 1 else 0) / sqrt (M.boundaryScale k)) ∧
      (∀ i k, matchingInnerFlux D M (ell k) i =
        if i = k then terminalCutoffSlope M u i else 0) ∧
      (∀ i k, modePairing D (L i) (F k) =
        if i = k then terminalCutoffEnergy M χ u i else 0) ∧
      (∀ i, ‖F i‖ ≤ sourceBound i) := by
  let L : Fin 2 → RadialModePair D := fun i =>
    terminalCapInnerLift hD M.innerLeft M.innerRight (M.boundaryScale i) (hχ i) (hu i)
  let F : Fin 2 → RadialModePair D := fun i =>
    terminalCapInnerSource M.innerLeft M.innerRight (M.boundaryScale i) (χ i) (u i) (hf i)
  let ell : Fin 2 → ℝ → ℝ := fun i => modeInnerExtension M.innerLeft M.innerRight
    (terminalCapLift (M.boundaryScale i) (χ i) (u i))
  have hrep (i : Fin 2) : ((L i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell i :=
    terminalCapInnerLift_ae hD M.innerLeft M.innerRight (M.boundaryScale i) (hχ i) (hu i)
  have hext (i : Fin 2) : EqOn (ell i)
      (terminalCapLift (M.boundaryScale i) (χ i) (u i)) (Icc M.innerLeft M.innerRight) :=
    modeInnerExtension_eqOn _ _ _
  have hFrep (i : Fin 2) : ((F i).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      terminalCapHilbertSource (M.boundaryScale i) D.w (χ i) (u i) :=
    terminalCapInnerSource_ae (hf i) (hderiv i)
  have hFfix (i : Fin 2) : modeInnerSource D M.innerLeft M.innerRight (F i) = F i :=
    modeInnerSource_idempotent D M.innerLeft M.innerRight _
  have hFscalar (i : Fin 2) : (F i).2 = 0 := rfl
  have hother (i k : Fin 2) (hik : i ≠ k) :
      χ i =ᶠ[𝓝 (matchingCut D M k)] fun _ => (0 : ℝ) := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hi
    have hk : matchingCut D M k ∈ tsupport (χ k) := by
      apply subset_tsupport (χ k)
      change χ k (matchingCut D M k) ≠ 0
      rw [(hown k).eq_of_nhds]
      exact one_ne_zero
    exact Set.disjoint_left.mp (hsep i k hik) hi hk
  have hg := matchingProfileGeometry hD
  have hr (i : Fin 2) : 0 < matchingCut D M i :=
    hg.1.trans (hsub (matchingCut_mem_innerIcc hlh i)).1
  have hw (i : Fin 2) : 0 < D.w (matchingCut D M i) :=
    hg.2.2.2.2.1 _ (hsub (matchingCut_mem_innerIcc hlh i))
  have hlam (i : Fin 2) : 0 < M.boundaryScale i := by
    rw [hscale i]
    exact standInBoundaryScale_pos (sq_pos_of_pos hfreq) (hw i) (hr i)
  refine ⟨L, F, ell, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    ?_, hrep, ?_, ?_, fun _ => rfl, hFscalar, hFfix, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact terminalCapInnerLift_equation hD (hχ i) (hu i)
      (Ioo_subset_Icc_self.trans hsub) (heq i) (hf i)
  · intro i
    exact (terminalCapInnerLift_representative_smooth M.innerLeft M.innerRight
      (M.boundaryScale i) (hχ i) (hu i)).of_le (by simp)
  · intro i r hrout
    apply modeInnerExtension_zero_outside
    rcases hrout with hl | hh
    · exact Or.inl hl.2
    · exact Or.inr hh.1
  · intro i r hri
    rw [hext i hri]
    by_cases hc : referenceColumn D r = 0
    · rw [hc, zero_mul]
    · have hz : χ i r = 0 := by
        by_contra hne
        exact Set.disjoint_left.mp (hcolumn i)
          (subset_tsupport _ hc) (subset_tsupport _ hne)
      simp only [terminalCapLift, hz, zero_mul, zero_div, mul_zero]
  · intro i k
    rw [hext i (matchingCut_mem_innerIcc hlh k)]
    exact terminalCapLift_matching_trace M χ u hown hother hvalue i k
  · intro i k
    rw [matchingInnerFlux_congr hlh (hext k) i]
    have hflux := terminalCapLift_matching_flux M hlh χ u hχ hu hown hother
      hvalue hscale hfreq hw hr k i
    by_cases hik : i = k
    · subst k
      exact hflux
    · simpa only [terminalCutoffSlope, if_neg hik, if_neg (Ne.symm hik)] using hflux
  · intro i k
    by_cases hik : i = k
    · subst k
      rw [if_pos rfl]
      exact terminalModeLiftSource_pairing_energy hD hlh.le hsub (hlam i)
        (hχ i) (hu i) (hrep i) (hext i) (hFrep i) (hFfix i) (hFscalar i) (hderiv i)
    · rw [if_neg hik]
      exact terminalModeLiftSource_pairing_zero hD hlh.le hsub
        (hrep i) (hext i) (hFrep k) (hFfix k) (hFscalar k) (hsep i k hik)
  · intro i
    exact (terminalCapInnerSource_norm_le_eLpNorm M.innerLeft M.innerRight
      (M.boundaryScale i) (χ i) (u i) (hf i)).trans (hsource i)

end ContinuousFlexibility.Radial
