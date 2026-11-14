module

public import ContinuousFlexibility.Radial.MatchedMorseSignedWeights
public import ContinuousFlexibility.Radial.MatchedInnerWeightTransport

/-!
# The same signed finite-chain inverse in the actual matching norm

The original supported multipliers are exactly the field multiplication
equivalences used on the original mode pair. Frozen uniqueness then
identifies the same C.inverse with the final M.innerInverse. The sole
change of Hilbert versus maximum pair norm costs sqrt 2.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section SameInverse

variable {D : ReferenceData}
  (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
  (hw : ContDiff ℝ ∞ D.w) (N K : ℕ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
  (hleft : M.innerLeft = G.left 0)
  (hright : M.innerRight = G.right (Fin.last (2 * (2 * K + 1))))
  (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
  (central : Fin (2 * (2 * K + 1) + 1)) (column : RadialModeL2 D)
  (hcolumn : column = matchingBorderVector D hD hB)
  (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
    (Ioo (G.left central) (G.right central)) column = column)
  {b : Bool} {j : ℝ} (C : InnerRadialActualChain D G b j central column)
  (hbool : b = decide (M.frequency = 2)) (hfreq : j = (M.frequency : ℝ))
  (hS : IsUnit C.fluxMatrix)
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)
  (CW : ℝ)
  (hCW : ∀ sign x, |matchedMorseSignedWeight N K G l r sign x| ≤ CW)

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
local notation "Out" => fun sign => matchedModeActualWeight D
  (Wo sign) (hWo sign) (ho sign) CW Co (hOut sign) (hOutInv sign)
local notation "In" => fun sign => matchedModeActualWeight D
  (Wi sign) (hWi sign) (hi sign) CW CW (hCW sign) (hInInv sign)

include hD hB hM hleft hright hsub hcolumn hcolfix hbool hfreq

theorem matchedInnerActualInverse_morse_loss_weighted
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hbound : ∀ sign : Bool,
      ‖innerSupportedWeightMultiplier (radialHilbertMeasure D)
          (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
          b (Wo sign) (hWo sign) CW (hOut sign) ∘L
        C.inverse hw hS ∘L
        innerSupportedWeightMultiplier (radialHilbertMeasure D)
          (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
          b (Wi (!sign)) (hWi (!sign)) CW (hCW (!sign))‖ ≤ B)
    (sign : Bool) :
    ‖(Out sign : RadialModePair D →L[ℝ] RadialModePair D) ∘L M.innerInverse ∘L
      matchingSourceInnerCLM D M hM ∘L matchedModeScalarGate D (decide (M.frequency = 2)) ∘L
      ((In sign).symm : RadialModePair D →L[ℝ] RadialModePair D)‖ ≤ sqrt 2 * B := by
  subst b
  subst j
  apply matchedInnerActualInverse_weighted_opNorm_le hD hB hw G M hM
    hleft hright hsub central column hcolumn hcolfix C hS
    (Wo sign) (Wi sign) (hWo sign) (hWi sign) (ho sign) (hi sign)
    CW Co CW CW (hOut sign) (hOutInv sign) (hCW sign) (hInInv sign) hB₀
  rw [innerSupportedWeightEquiv_toCLM, innerSupportedWeightEquiv_symm_toCLM]
  have he :
      innerSupportedWeightMultiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
        (decide (M.frequency = 2)) (fun x => (Wi sign x)⁻¹) (hWi sign).inv CW (hInInv sign) =
      innerSupportedWeightMultiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
        (decide (M.frequency = 2)) (Wi (!sign)) (hWi (!sign)) CW (hCW (!sign)) := by
    apply innerSupportedWeightMultiplier_congr
    exact matchedMorseSignedWeight_inv N K G l r sign
  rw [he]
  exact hbound sign

end SameInverse

end ContinuousFlexibility.Radial
