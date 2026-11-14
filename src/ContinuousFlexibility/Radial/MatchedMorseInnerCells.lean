module

public import ContinuousFlexibility.Radial.MatchedInnerInterpolationWalls
public import ContinuousFlexibility.Radial.MatchedMorseLocalizerWeights
public import ContinuousFlexibility.Radial.MatchedMorseInnerWeightTransfer
public import ContinuousFlexibility.Radial.MatchedInnerSupportedCells

/-!
# Actual later inner two-channel kernels

The same finite-chain inverse supplies the signed operator estimates.
The actual nonzero localizers supply the signed pointwise comparisons.
These two independently proved ingredients yield the true restricted
matching inverse kernel, with its original scalar gate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section OriginalLaterChain

variable {T : MorseChainData} {σ₀ : ℕ → ℝ} {old : ReferenceData} {cost : ℕ → ℝ}
  (h : MorseChainRealization T σ₀ old cost) (κ : Bool → ℝ) (hκ : ∀ side, 0 < κ side)
  {N K : ℕ} (hN : T.index ≤ N) (hlarge : 4096 ≤ N) {center : Fin 2 → ℝ}
  (hc : center 0 < center 1)
  (hcl : κ false * innerMorseChainCut T false N 1 < center 0)
  (hcr : center 1 < κ true * innerMorseChainCut T true N 0)
  (D : ReferenceData) (hD : RadialProfileGeometry D) (hK : 0 < K)
  (hLcore : scaledMorseInnerOuterPoint T κ N K false ∈ radialCore D)
  (hRcore : scaledMorseInnerOuterPoint T κ N K true ∈ radialCore D)
  (e : ℝ ≃o ℝ)
  (he : ∀ side x, (if side then morseChainSeam T true N ≤ x
    else x ≤ morseChainSeam T false N) → e.symm x = κ side * x)
  (hχ : ∀ m x, D.localizer m x = old.localizer m (e x))
  {J : ℕ} (hJ : N ≤ J)
  (hwindow : ∀ m, old.cellIndex m ≤ N → ∀ y, old.localizer m y ≠ 0 →
    y ∈ Icc (morseChainSeam T false J) (morseChainSeam T true J))

local notation "G" => scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore
local notation "centralSlot" => innerModelChainPiece (innerMorseInnerCenter K)

variable (hAcc : IsAccumulatingProfile D) (hBorder : RadialTrueBorder D)
  (hP : RadialPartition D) (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
  (hleft : M.innerLeft = (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).left 0)
  (hright : M.innerRight = (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).right (Fin.last (2 * (2 * K + 1))))
  (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
  (column : RadialModeL2 D)
  (hcolumn : column = matchingBorderVector D hAcc hBorder)
  (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
    (Ioo ((scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).left (innerModelChainPiece (innerMorseInnerCenter K))) ((scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore).right (innerModelChainPiece (innerMorseInnerCenter K)))) column = column)
  {b : Bool} {j : ℝ} (C : InnerRadialActualChain D (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore) b j (innerModelChainPiece (innerMorseInnerCenter K)) column)
  (hbool : b = decide (M.frequency = 2)) (hfreq : j = (M.frequency : ℝ))
  (hS : IsUnit C.fluxMatrix)
  (CW : ℝ)
  (hCW : ∀ sign x, |matchedMorseSignedWeight N K (scaledMorseInnerChainGeometry h κ hκ hN hc hcl hcr D hD hK hLcore hRcore)
    C.matchedWeightLeft C.matchedWeightRight sign x| ≤ CW)

local notation "l" => C.matchedWeightLeft
local notation "r" => C.matchedWeightRight
local notation "Wi" => matchedMorseSignedWeight N K G l r
local notation "Wo" => matchedMorseLocalizedWeight N K G l r
local notation "hWi" => matchedMorseSignedWeight_measurable N K G l r
local notation "hWo" => matchedMorseLocalizedWeight_measurable N K G l r
local notation "hi" => matchedMorseSignedWeight_pos N K G l r
local notation "ho" => matchedMorseLocalizedWeight_pos N K G l r
local notation "hOut" => matchedMorseLocalizedWeight_bound N K G l r hCW
local notation "hOutInv" => matchedMorseLocalizedWeight_inv_bound N K G l r hCW
local notation "Co" => matchedMorseLossInverseBound N K * CW
local notation "hInInv" => fun sign x =>
  Eq.trans_le (congrArg abs (matchedMorseSignedWeight_inv N K G l r sign x))
    (hCW (!sign) x)

include hlarge he hχ hJ hwindow hAcc hBorder hM hleft hright hsub hcolumn hcolfix hbool hfreq

/-- The constant and the exponent depend on the initial seam window
and local model suppliers, not on the mode or retained length. -/
theorem matchedMorse_actual_inner_channel_bound
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ sign : Bool,
      ‖innerSupportedWeightMultiplier (radialHilbertMeasure D)
          (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
          b (Wo sign) (hWo sign) CW (hOut sign) ∘L
        C.inverse hD.2.2.1.1 hS ∘L
        innerSupportedWeightMultiplier (radialHilbertMeasure D)
          (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
          b (Wi (!sign)) (hWi (!sign)) CW (hCW (!sign))‖ ≤ B)
    (level : ℕ → ℕ) (hlevel₀ : level 0 = 0)
    (hlevel : ∀ m, level (m + 1) = old.cellIndex m)
    (k m : ℕ) :
    ‖matchedModeChannel D hP k ∘L M.innerInverse ∘L matchingSourceInnerCLM D M hM ∘L
      matchedModeScalarGate D (decide (M.frequency = 2)) ∘L matchedModeChannel D hP m‖ ≤
      (sqrt 2 * B) * (matchedMorseLocalizerWeightConstant N J) ^ 2 *
        exp (41414 * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|) := by
  apply matchedInner_twoSign_supported_cell_envelope hAcc hP M hM level hlevel₀
    Wo Wi hWo hWi ho hi (fun _ => CW) (fun _ => Co) (fun _ => CW) (fun _ => CW)
    hOut hOutInv hCW hInInv
    (mul_nonneg (sqrt_nonneg 2) hB)
    (matchedMorseLocalizerWeightConstant_ge_one N J)
  · intro sign
    exact matchedInnerActualInverse_morse_loss_weighted hAcc hBorder hD.2.2.1.1 N K G M hM
      hleft hright hsub centralSlot column hcolumn hcolfix C hbool hfreq hS l r CW hCW hB hbound sign
  · intro sign j
    have hs : |(if sign then (1 : ℝ) else -1)| ≤ 1 := by cases sign <;> norm_num
    have hh := matchedScaledMorse_localizer_weight_ae h κ hκ hN hlarge hc hcl hcr
      D hD hK hLcore hRcore e he hχ hJ hwindow hAcc l r hs j
    filter_upwards [hh] with x hx hχx hinner
    have hin : x ∈ Ioo ((G).left 0) ((G).right (Fin.last (2 * (2 * K + 1)))) := by
      simpa only [hleft, hright] using hinner
    have hb := hx hχx hin
    cases sign <;>
      simpa only [matchedMorseLocalizedWeight, matchedMorseSignedWeight, hlevel,
        Bool.false_eq_true, ite_false, ite_true, neg_one_mul, one_mul] using hb

end OriginalLaterChain

end ContinuousFlexibility.Radial
