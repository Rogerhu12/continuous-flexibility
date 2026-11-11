import ContinuousFlexibility.Radial.MatchedOuterGreenIdentification
import ContinuousFlexibility.Radial.MatchedOuterPoissonOrientation
import ContinuousFlexibility.Radial.MatchedPhysicalChannelComparison
import ContinuousFlexibility.Radial.MatchedPhysicalScalarGate
import ContinuousFlexibility.Radial.MatchingInverseFormula

/-!
# Whole-tail estimates for the same actual matching data

The all-source Green identity and the actual natural Robin line identify
the stored exterior inverse and Poisson columns. Restriction, extension,
the outer source projection and the scalar gate then give the exact
channels consumed by the matching formula.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements

theorem matchedOuter_actual_channels_of_whole_bounds
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hP : RadialPartition D) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ i, 0 < M.boundaryScale i)
    (hdiag : ∀ k l, k ≠ l → M.A k l = 0 ∧ M.B k l = 0)
    (hnorm : ∀ k, M.A k k ^ 2 + M.B k k ^ 2 = 1)
    (hsource : M.sourceOuter = modeOuterSource D M.innerLeft M.innerRight)
    {c : Bool → ℝ} {P ZP Q ZQ : Bool → ℝ → ℝ}
    (H : ∀ side : Bool, OuterFundamentalStatePair
      (fun x => M.boundaryScale (if side then 1 else 0) / outerTailOutwardWeight D side x)
      (fun x => (M.frequency : ℝ) ^ 2 * deriv (outerTailOutwardWeight D side) x /
        (M.boundaryScale (if side then 1 else 0) * x))
      (P side) (ZP side) (Q side) (ZQ side)
      (outerOutwardRadius side (if side then M.innerRight else M.innerLeft)) (c side)
      (outerOutwardRadius side (tailPhysicalEndpoint D side)))
    (hV : ∀ side, MemLp (H side).V 2
      (outerWholeMeasure D side (if side then M.innerRight else M.innerLeft)))
    (R : ∀ side, OuterWholeL2 D side (if side then M.innerRight else M.innerLeft) →L[ℝ]
      OuterWholeL2 D side (if side then M.innerRight else M.innerLeft))
    (hR : ∀ side f, (R side f : ℝ → ℝ) =ᵐ[
      outerWholeMeasure D side (if side then M.innerRight else M.innerLeft)] fun x =>
        ∫ y, outerGreenKernel (M.boundaryScale (if side then 1 else 0))
          (H side).U (H side).V x y * f y
          ∂outerWholeMeasure D side (if side then M.innerRight else M.innerLeft))
    (hline : ∀ side q, outerStatePair (H side).entrance q = 0 ↔
      outerStatePair (M.A (if side then 1 else 0) (if side then 1 else 0),
        M.B (if side then 1 else 0) (if side then 1 else 0)) q = 0)
    (level : ℕ → ℕ) (transition : ℕ) {C₀ Cₚ A : ℝ}
    (hC₀ : 0 ≤ C₀) (hCₚ : 0 ≤ Cₚ)
    (hkernel : ∀ side k m,
      ‖(matchedOuterCell D hP side
          (outerWholeMeasure D side (if side then M.innerRight else M.innerLeft)) k).comp
        ((R side).comp (matchedOuterCell D hP side
          (outerWholeMeasure D side (if side then M.innerRight else M.innerLeft)) m))‖ ≤
        C₀ * exp (A * (radialQ (level (k + 1)) + radialQ (level (m + 1))) -
          |radialS (level (k + 1)) - radialS (level (m + 1))|))
    (hcolumn : ∀ side m,
      ‖matchedOuterCell D hP side
        (outerWholeMeasure D side (if side then M.innerRight else M.innerLeft)) m
        ((sqrt (M.boundaryScale (if side then 1 else 0)))⁻¹ •
          (hV side).toLp (H side).V)‖ ≤
        Cₚ * exp (A * (radialQ (level (m + 1)) + radialQ transition) -
          |radialS (level (m + 1)) - radialS transition|)) :
    (∀ active k m,
      ‖matchedModeChannel D hP k ∘L M.outerInverse ∘L
        matchingSourceOuterCLM D M hM ∘L
        (matchedModeScalarGate D active ∘L matchedModeChannel D hP m)‖ ≤
        (2 * C₀) * exp (A * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|)) ∧
    (∀ k i, ‖matchedModeChannel D hP k (M.outerPoisson i)‖ ≤
      Cₚ * exp (A * (radialQ (level k) + radialQ transition) -
        |radialS (level k) - radialS transition|)) := by
  classical
  let cut : Bool → ℝ := fun side => if side then M.innerRight else M.innerLeft
  let G := matchedOuterSeparatedInverse D cut R
  have hG : M.outerInverse = G :=
    matchedOuterInverse_eq_separatedGreen hD hB M ha hm hb hscale H hV R hR hline
      (matchingOuterRealizations_of_local hM)
  have hremove (active : Bool) :
      M.outerInverse ∘L matchingSourceOuterCLM D M hM ∘L
        matchedModeScalarGate D active = M.outerInverse := by
    ext F
    simp only [ContinuousLinearMap.comp_apply, matchingSourceOuterCLM_apply, hsource, hG]
    rw [matchedOuterSeparatedInverse_sourceOuter D cut hm R]
    simp only [G, matchedOuterSeparatedInverse_apply, matchedModeScalarGate_apply]
  have hborderLeft :
      (matchedModeBorder D).comp M.outerInverse = 0 := by
    ext F
    simp only [ContinuousLinearMap.comp_apply, hG, G, matchedModeBorder_apply,
      matchedOuterSeparatedInverse_scalar, ContinuousLinearMap.zero_apply]
  have hborderRight :
      M.outerInverse.comp (matchedModeBorder D) = 0 := by
    ext F
    simp only [ContinuousLinearMap.comp_apply, hG, G, matchedModeBorder_apply,
      matchedOuterSeparatedInverse_apply, map_zero, add_zero,
      ContinuousLinearMap.zero_apply]
  constructor
  · intro active k m
    have heq :
        matchedModeChannel D hP k ∘L M.outerInverse ∘L
          matchingSourceOuterCLM D M hM ∘L
          (matchedModeScalarGate D active ∘L matchedModeChannel D hP m) =
        matchedModeChannel D hP k ∘L M.outerInverse ∘L matchedModeChannel D hP m := by
      ext F
      have hr := congrArg
        (fun T : RadialModePair D →L[ℝ] RadialModePair D =>
          T (matchedModeChannel D hP m F)) (hremove active)
      simpa only [ContinuousLinearMap.comp_apply] using
        congrArg (matchedModeChannel D hP k) hr
    rw [heq]
    cases k with
    | zero =>
        simp only [matchedModeChannel, ← ContinuousLinearMap.comp_assoc, hborderLeft,
          ContinuousLinearMap.zero_comp, norm_zero]
        positivity
    | succ k =>
        cases m with
        | zero =>
            simp only [matchedModeChannel, ContinuousLinearMap.comp_assoc, hborderRight,
              ContinuousLinearMap.comp_zero, norm_zero]
            positivity
        | succ m =>
            change ‖(matchedModeCell D hP k).comp
              (M.outerInverse.comp (matchedModeCell D hP m))‖ ≤ _
            rw [hG]
            calc
              _ ≤ _ := norm_matchedOuterSeparatedInverse_cells_le D hP cut R k m
              _ ≤ C₀ * exp (A * (radialQ (level (k + 1)) +
                    radialQ (level (m + 1))) -
                    |radialS (level (k + 1)) - radialS (level (m + 1))|) +
                  C₀ * exp (A * (radialQ (level (k + 1)) +
                    radialQ (level (m + 1))) -
                    |radialS (level (k + 1)) - radialS (level (m + 1))|) :=
                add_le_add (hkernel false k m) (hkernel true k m)
              _ = _ := by ring
  · intro k i
    cases k with
    | zero =>
        have hz : (M.outerPoisson i).2 = 0 := (hM.2.2.2.2.2 i).2.2.2.2.2.2.1
        simp only [matchedModeChannel, matchedModeBorder_norm, hz, norm_zero]
        positivity
    | succ k =>
        have hs (side : Bool) :
            ‖matchedModeCell D hP k (M.outerPoisson (if side then 1 else 0))‖ ≤
              Cₚ * exp (A * (radialQ (level (k + 1)) + radialQ transition) -
                |radialS (level (k + 1)) - radialS transition|) := by
          rw [matchedOuterPoisson_norm_eq_natural hD hB hM ha hm hb hscale hdiag hnorm
            side (H side) (hV side) (hline side) (matchedModeCell D hP k),
            norm_matchedModeCell_naturalPoisson]
          exact hcolumn side k
        fin_cases i
        · exact hs false
        · exact hs true

end ContinuousFlexibility.Radial
