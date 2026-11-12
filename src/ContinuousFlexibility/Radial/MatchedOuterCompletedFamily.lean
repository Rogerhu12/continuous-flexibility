import ContinuousFlexibility.Radial.MatchedOuterUniformRetainedEnvelope
import ContinuousFlexibility.Radial.MatchedOuterMatchingTransfer
import ContinuousFlexibility.Radial.MatchedModeCellBounds
import ContinuousFlexibility.Radial.ReferenceRawKernelSchur

/-!
# Uniform outer channels of the same completed matching family

The actual retained profile constructs the whole kernels and normalized
natural columns. The stored matching inverses and columns are identified
with them by the original graph uniqueness and natural Robin line.
Constants are chosen before the modal index and all channel labels.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

theorem SeedRetainedPair.exists_uniform_selectedOuter_matching_bounds
    {S : SelectedTailData} {K₀ : SeedCentralCutoff} {q length Cstar : ℝ} {requested : ℕ}
    (P : SeedRetainedPair S K₀ q length) (metadata : R10aSelectedMetadata Cstar requested S)
    (Γ : ConnectedReferenceGeometry)
    (hE : IsAccumulatingProfile Γ.reference) (hB : RadialTrueBorder Γ.reference)
    (hPE : RadialPartition Γ.reference)
    (hw : Γ.reference.w = P.pair.profile) (hcoordinates : R11aRetainedCoordinates P Γ)
    (W : ℕ → TerminalRegionalData Γ.reference)
    (G : ℕ → RadialModePair Γ.reference →L[ℝ] RadialModePair Γ.reference)
    (hactual : ∀ i, ActualMatchedRepresentation Γ.reference (G i) (W i).matching)
    (hj : ∀ i, 2 ≤ (W i).matching.frequency)
    (heven : ∀ i, Even (W i).matching.frequency)
    (hband : ∀ i, radialFrequencyBand S.chain S.Cstar
      (W i).matching.transitionIndex (W i).matching.frequency)
    (hleft : ∀ i, (W i).matching.innerLeft =
      P.sideRadius false * S.joinInner false (W i).matching.transitionIndex)
    (hright : ∀ i, (W i).matching.innerRight =
      P.sideRadius true * S.joinInner true (W i).matching.transitionIndex)
    (hsource : ∀ i, (W i).matching.sourceOuter =
      modeOuterSource Γ.reference (W i).matching.innerLeft (W i).matching.innerRight)
    (v : ℕ → Bool → ℝ → ℝ)
    (hv : ∀ i side, ContDiff ℝ ∞ (v i side))
    (hN : ∀ i side, RadialNaturalTail Γ.reference side (W i).matching.frequency
      (if side then (W i).matching.innerRight else (W i).matching.innerLeft) (v i side))
    (hAB : ∀ i side,
      (W i).matching.A (if side then 1 else 0) (if side then 1 else 0) =
        (outerUnitState (selectedBoundaryState Γ.reference (W i).matching.frequency
          (r07OutwardSign side)
          (if side then (W i).matching.innerRight else (W i).matching.innerLeft)
          (v i side))).1 ∧
      (W i).matching.B (if side then 1 else 0) (if side then 1 else 0) =
        (outerUnitState (selectedBoundaryState Γ.reference (W i).matching.frequency
          (r07OutwardSign side)
          (if side then (W i).matching.innerRight else (W i).matching.innerLeft)
          (v i side))).2) :
    ∃ CO aO CPO bO : ℝ, 0 < CO ∧ 0 ≤ aO ∧ 0 < CPO ∧ 0 ≤ bO ∧
      (∀ i k m,
        ‖matchedModeChannel Γ.reference hPE k ∘L (W i).matching.outerInverse ∘L
          matchingSourceOuterCLM Γ.reference (W i).matching
            (actualMatchedRepresentation_localRealizations (hactual i)) ∘L
          (matchedModeScalarGate Γ.reference (decide (i = 0)) ∘L
            matchedModeChannel Γ.reference hPE m)‖ ≤
          CO * exp (aO *
            (radialQ (referenceRawChannelLevel (S.family S.sigma) k) +
              radialQ (referenceRawChannelLevel (S.family S.sigma) m)) -
            |radialS (referenceRawChannelLevel (S.family S.sigma) k) -
              radialS (referenceRawChannelLevel (S.family S.sigma) m)|)) ∧
      (∀ i k t, ‖matchedModeChannel Γ.reference hPE k ((W i).matching.outerPoisson t)‖ ≤
        CPO * exp (bO *
          (radialQ (referenceRawChannelLevel (S.family S.sigma) k) +
            radialQ (W i).matching.transitionIndex) -
          |radialS (referenceRawChannelLevel (S.family S.sigma) k) -
            radialS (W i).matching.transitionIndex|)) := by
  classical
  obtain ⟨C, A, hC, hA, hall⟩ :=
    P.exists_uniform_selectedOuter_tailEnvelope metadata Γ hE hPE hw hcoordinates
  have hone (i : ℕ) :
      (∀ k m,
        ‖matchedModeChannel Γ.reference hPE k ∘L (W i).matching.outerInverse ∘L
          matchingSourceOuterCLM Γ.reference (W i).matching
            (actualMatchedRepresentation_localRealizations (hactual i)) ∘L
          (matchedModeScalarGate Γ.reference (decide (i = 0)) ∘L
            matchedModeChannel Γ.reference hPE m)‖ ≤
          (2 * C) * exp (A *
            (radialQ (referenceRawChannelLevel (S.family S.sigma) k) +
              radialQ (referenceRawChannelLevel (S.family S.sigma) m)) -
            |radialS (referenceRawChannelLevel (S.family S.sigma) k) -
              radialS (referenceRawChannelLevel (S.family S.sigma) m)|)) ∧
      (∀ k t, ‖matchedModeChannel Γ.reference hPE k ((W i).matching.outerPoisson t)‖ ≤
        C * exp (A *
          (radialQ (referenceRawChannelLevel (S.family S.sigma) k) +
            radialQ (W i).matching.transitionIndex) -
          |radialS (referenceRawChannelLevel (S.family S.sigma) k) -
            radialS (W i).matching.transitionIndex|)) := by
    let M := (W i).matching
    let cut : Bool → ℝ := fun side => if side then M.innerRight else M.innerLeft
    have ht (side : Bool) :
        MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE side (cut side)
          M.frequency M.transitionIndex C A := by
      have hh := hall M.transitionIndex M.frequency (hj i) (heven i) (hband i) side
      change MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE side
        (P.sideRadius side * S.joinInner side (W i).matching.transitionIndex)
        (W i).matching.frequency (W i).matching.transitionIndex C A at hh
      cases side
      · change MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE false
          (W i).matching.innerLeft (W i).matching.frequency
          (W i).matching.transitionIndex C A
        rw [hleft i]
        exact hh
      · change MatchedOuterTailEnvelope (S.family S.sigma) Γ.reference hPE true
          (W i).matching.innerRight (W i).matching.frequency
          (W i).matching.transitionIndex C A
        rw [hright i]
        exact hh
    have hs (side : Bool) :
        standInBoundaryScale ((M.frequency : ℝ) ^ 2) (Γ.reference.w (cut side)) (cut side) =
          M.boundaryScale (if side then 1 else 0) := by
      cases side
      · change standInBoundaryScale (((W i).matching.frequency : ℝ) ^ 2)
          (Γ.reference.w (W i).matching.innerLeft) (W i).matching.innerLeft =
            (W i).matching.boundaryScale (0 : Fin 2)
        simpa [matchingCut] using ((W i).boundary_scale 0).symm
      · change standInBoundaryScale (((W i).matching.frequency : ℝ) ^ 2)
          (Γ.reference.w (W i).matching.innerRight) (W i).matching.innerRight =
            (W i).matching.boundaryScale (1 : Fin 2)
        simpa [matchingCut] using ((W i).boundary_scale 1).symm
    have ht' := ht
    conv at ht' =>
      intro side
      unfold MatchedOuterTailEnvelope
      rw [hs side]
    choose c P₀ ZP Q ZQ H hV R hR hline hkernel hcolumn using ht'
    have hline' (side : Bool) (z : ℝ × ℝ) :
        outerStatePair (H side).entrance z = 0 ↔
          outerStatePair (M.A (if side then 1 else 0) (if side then 1 else 0),
            M.B (if side then 1 else 0) (if side then 1 else 0)) z = 0 := by
      rw [(hAB i side).1, (hAB i side).2]
      exact hline side (v i side) (hv i side) (hN i side) z
    have hb := matchedOuter_actual_channels_of_whole_bounds hE hB hPE M
      (actualMatchedRepresentation_localRealizations (hactual i))
      (W i).cut_order.1 (W i).cut_order.2.1 (W i).cut_order.2.2
      (fun t => ((W i).diagonal t).1)
      (W i).boundary_off_diagonal (W i).boundary_normalized (hsource i)
      (c := c) (P := P₀) (ZP := ZP) (Q := Q) (ZQ := ZQ)
      H hV R hR hline' (referenceRawChannelLevel (S.family S.sigma)) M.transitionIndex
      (C₀ := C) (Cₚ := C) (A := A) hC.le hC.le
      (fun side k m => by
        simpa only [referenceRawChannelLevel] using hkernel side k m)
      (fun side m => by
        simpa only [referenceRawChannelLevel] using hcolumn side m)
    exact ⟨hb.1 (decide (i = 0)), hb.2⟩
  exact ⟨2 * C, A, C, A, mul_pos (by norm_num) hC, hA.le, hC, hA.le,
    fun i => (hone i).1, fun i => (hone i).2⟩

end ContinuousFlexibility.Radial
