module

public import ContinuousFlexibility.Radial.MatchedInnerCompactEnvelope
public import ContinuousFlexibility.Radial.MatchedModeCellBounds
public import ContinuousFlexibility.Radial.R07LaterSelection

/-!
# A uniform spatial bound for the actual finite first band

The original first frequency band is finite. The exact compact-support
envelopes of its actual matching operators therefore have one common
constant. Both the modal operator and the Poisson columns remain the
ones in the completed actual matching records.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real ContinuousFlexibility.Statements

/-- A finite family of the existing inner operators has a common
constant. No norm bound or spatial envelope is an input. -/
theorem matchedInner_finite_spatial_envelope {ι : Type*} [Finite ι]
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (M : ι → RadialMatchingData D) (hM : ∀ t, MatchingLocalRealizations D (M t))
    (hcore : ∀ t, Icc (M t).innerLeft (M t).innerRight ⊆ radialCore D)
    (level : ℕ → ℕ) (base : ℕ) (active : ι → Bool) :
    ∃ C : ℝ, 0 < C ∧
      (∀ t k m,
        ‖matchedModeChannel D hP k ∘L (M t).innerInverse ∘L
          matchingSourceInnerCLM D (M t) (hM t) ∘L matchedModeScalarGate D (active t) ∘L
            matchedModeChannel D hP m‖ ≤
          C * exp (-|radialS (level k) - radialS (level m)|)) ∧
      ∀ t k i,
        ‖matchedModeChannel D hP k ((M t).innerPoisson i)‖ ≤
          C * exp (-|radialS (level k) - radialS base|) := by
  classical
  choose C hC hblock hcolumn using fun t =>
    matchedInner_compact_spatial_envelope hD hP (M t) (hM t) (hcore t) level base (active t)
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  have hCB (t : ι) : C t ≤ max B 0 + 1 := by
    have ht := hB ⟨t, rfl⟩
    linarith only [ht, le_max_left B 0]
  refine ⟨max B 0 + 1, by positivity, ?_, ?_⟩
  · intro t k m
    exact (hblock t k m).trans
      (mul_le_mul_of_nonneg_right (hCB t) (exp_pos _).le)
  · intro t k i
    exact (hcolumn t k i).trans
      (mul_le_mul_of_nonneg_right (hCB t) (exp_pos _).le)

/-- The positive even-mode numbering has a finite preimage of the
original first band. -/
theorem matched_firstModeIndices_finite (T : MorseChainData) (Cstar : ℝ) :
    Set.Finite {q : ℕ | radialFrequencyBand T Cstar T.index (2 * (q + 1))} := by
  let f : ℕ → ℕ := fun q => 2 * (q + 1)
  have hf : Set.InjOn f
      (f ⁻¹' {j : ℕ | 2 ≤ j ∧ Even j ∧ radialFrequencyBand T Cstar T.index j}) := by
    intro a _ b _ hab
    dsimp only [f] at hab
    omega
  have hfinite := Set.Finite.preimage hf (r07_first_band_finite T Cstar)
  apply hfinite.subset
  intro q hq
  change 2 ≤ 2 * (q + 1) ∧ Even (2 * (q + 1)) ∧
    radialFrequencyBand T Cstar T.index (2 * (q + 1))
  exact ⟨by omega, ⟨q + 1, by omega⟩, hq⟩

/-- The first-band part of the same completed matching family has both
canonical spatial envelopes, with loss exponent zero. The labeling may
be the original canonical labels, before the final index floor. -/
theorem matchedInner_actual_firstBand_spatial_envelope {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : ℕ → RadialModePair D →L[ℝ] RadialModePair D)
    (M : ℕ → RadialMatchingData D)
    (hactual : ∀ q, ActualMatchedRepresentation D (G q) (M q))
    (hfrequency : ∀ q, (M q).frequency = 2 * (q + 1))
    (T : MorseChainData) (Cstar : ℝ) (level : ℕ → ℕ) (active : ℕ → Bool) :
    ∃ C : ℝ, 0 < C ∧
      (∀ q, radialFrequencyBand T Cstar T.index (M q).frequency → ∀ k m,
        ‖matchedModeChannel D hP k ∘L (M q).innerInverse ∘L
          matchingSourceInnerCLM D (M q) (actualMatchedRepresentation_localRealizations (hactual q)) ∘L
            matchedModeScalarGate D (active q) ∘L matchedModeChannel D hP m‖ ≤
          C * exp (-|radialS (level k) - radialS (level m)|)) ∧
      ∀ q, radialFrequencyBand T Cstar T.index (M q).frequency → ∀ k i,
        ‖matchedModeChannel D hP k ((M q).innerPoisson i)‖ ≤
          C * exp (-|radialS (level k) - radialS T.index|) := by
  classical
  let J := {q : ℕ // radialFrequencyBand T Cstar T.index (2 * (q + 1))}
  letI : Fintype J := (matched_firstModeIndices_finite T Cstar).fintype
  have hlocal (q : ℕ) := actualMatchedRepresentation_localRealizations (hactual q)
  have hcore (q : ℕ) :
      Icc (M q).innerLeft (M q).innerRight ⊆ radialCore D := by
    intro r hr
    exact ⟨(hactual q).1.trans_le hr.1, hr.2.trans_lt (hactual q).2.2.1⟩
  obtain ⟨C, hC, hblock, hcolumn⟩ :=
    matchedInner_finite_spatial_envelope hD hP
      (fun q : J => M q.val) (fun q => hlocal q.val) (fun q => hcore q.val)
      level T.index (fun q => active q.val)
  refine ⟨C, hC, ?_, ?_⟩
  · intro q hq k m
    have hj : radialFrequencyBand T Cstar T.index (2 * (q + 1)) := by
      simpa only [hfrequency q] using hq
    exact hblock ⟨q, hj⟩ k m
  · intro q hq k i
    have hj : radialFrequencyBand T Cstar T.index (2 * (q + 1)) := by
      simpa only [hfrequency q] using hq
    exact hcolumn ⟨q, hj⟩ k i

end ContinuousFlexibility.Radial
