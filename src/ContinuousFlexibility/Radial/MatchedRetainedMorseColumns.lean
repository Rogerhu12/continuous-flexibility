import ContinuousFlexibility.Radial.MatchedRetainedMorseWeights
import ContinuousFlexibility.Radial.MatchedInnerInterpolationWalls

/-!
# The actual finite-chain weight on retained Morse columns

The physical interpolation is the original chain weight with the walls
of the same actual dictionary. Its pullback and its endpoint restriction
are computed here, so the normalized column estimate has no assumed
physical interpolation identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

namespace SeedRetainedPair

variable {S : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K₀ q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (K : ℕ) (H : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (bordered : Bool) (j : ℝ) (column : RadialModeL2 D)
  (side : Bool) (p : Fin K)

local notation "m" => innerMorseInnerTailIndex S.chain.index K side p
local notation "center" => innerModelChainPiece (innerMorseInnerCenter K)
local notation "piece" => innerModelChainPiece (innerMorseInnerTailSlot K side p)

variable
  (hleft : H.left (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
    P.sideRadius side * innerMorseChainCut S.chain side
      (innerMorseInnerTailIndex S.chain.index K side p) 0)
  (hright : H.right (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
    P.sideRadius side * innerMorseChainCut S.chain side
      (innerMorseInnerTailIndex S.chain.index K side p) 1)
  {CM KM : ℝ}
  (hB : BufferHypotheses
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index K side p) : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index K side p))
      j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index K side p) : ℝ) ^ 9)) CM KM)

local notation "A" => P.retainedMorseModelChart hw hS G₀ hfirst H bordered j center piece column
  side m (And.left (innerMorseInnerTailIndex_bounds S.chain.index K side p))
  (innerMorseInnerTailPiece_ne_center K side p) hleft hright hB M

variable
  (C : InnerRadialActualChain D H bordered j
    (innerModelChainPiece (innerMorseInnerCenter K)) column)
  (hpiece : C.piece (innerModelChainPiece (innerMorseInnerTailSlot K side p)) =
    .inl (P.retainedMorseModelChart hw hS G₀ hfirst H bordered j
      (innerModelChainPiece (innerMorseInnerCenter K))
      (innerModelChainPiece (innerMorseInnerTailSlot K side p)) column
      side (innerMorseInnerTailIndex S.chain.index K side p)
      (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
      (innerMorseInnerTailPiece_ne_center K side p) hleft hright hB M))

include hleft hright hB hpiece

/-- Both real signs are estimates of the actual model column inside
the same physical finite-chain weight and the same interface diagonal. -/
theorem retainedMorseModelChart_actual_weighted_column_bound
    {a γ σ : ℝ} (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hσ : |σ| ≤ 1)
    (hN : 4096 ≤ S.chain.index) (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (hj : 1 ≤ j) (hCM : 0 < CM)
    (hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / j)
    (CW : ℝ) (hCW : ∀ x,
      |(innerMorseInnerWeight S.chain.index K a γ H
        C.matchedWeightLeft C.matchedWeightRight x) ^ σ| ≤ CW)
    (i : Fin 2) :
    ‖(innerChainScalarRestriction (2 * (2 * K + 1)) piece
        (fun k => (innerMorseInnerInterfaceWeight S.chain.index K a γ k) ^ σ) 1 i *
        sqrt ((A).kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D)
          (fun x => (innerMorseInnerWeight S.chain.index K a γ H
            C.matchedWeightLeft C.matchedWeightRight x) ^ σ)
          ((innerMorseInnerWeight_measurable S.chain.index K a γ H
            C.matchedWeightLeft C.matchedWeightRight).pow_const σ) CW hCW) ((A).column i)‖ ≤
      innerMorsePoissonConstant / j := by
  have hcut :
      innerChainScalarRestriction (2 * (2 * K + 1)) piece
        (fun k => (innerMorseInnerInterfaceWeight S.chain.index K a γ k) ^ σ) 1 i =
      (innerMorseCutWeight S.chain.index a γ side m i) ^ σ := by
    simpa only [one_rpow, innerMorseInnerInterfaceWeight_model,
      innerMorseInnerModelWeight_tail] using
      innerChainScalarRestriction_map (2 * (2 * K + 1)) piece
        (innerMorseInnerInterfaceWeight S.chain.index K a γ) 1 (fun z : ℝ => z ^ σ) i
  have hinterp (x : ℝ) (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA S.chain m) (morseChainB S.chain m))) :
      (innerMorseInnerWeight S.chain.index K a γ H
        C.matchedWeightLeft C.matchedWeightRight
        (P.sideRadius side * S.chain.radius side m x)) ^ σ =
      (innerMorseInterpolatedWeight S.chain.index a γ side m
        (P.sideRadius side * S.chain.radius side m (bufferInnerWall
          (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) j
            (8 * (S.chain.d m : ℝ) ^ 9)) 0))
        (P.sideRadius side * S.chain.radius side m (bufferInnerWall
          (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) j
            (8 * (S.chain.d m : ℝ) ^ 9)) 1))
        (P.sideRadius side * S.chain.radius side m x)) ^ σ := by
    have h := C.matchedWeight_on_closed_model S.chain.index K a γ
      (innerMorseInnerTailSlot K side p) A hpiece hx
    simpa only [retainedMorseModelChart, innerMorseInnerModelWeight_tail,
      innerMorseInterpolatedWeight] using congrArg (fun z : ℝ => z ^ σ) h
  rw [hcut]
  exact P.retainedMorseModelChart_weighted_column_bound hw hS G₀ hfirst H bordered j
    center piece column side m (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (innerMorseInnerTailPiece_ne_center K side p) hleft hright hB M
    S.chain.index ha hN hNa (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    hj hCM hrem γ σ hγ hσ
    (fun x => (innerMorseInnerWeight S.chain.index K a γ H
      C.matchedWeightLeft C.matchedWeightRight x) ^ σ)
    ((innerMorseInnerWeight_measurable S.chain.index K a γ H
      C.matchedWeightLeft C.matchedWeightRight).pow_const σ) CW hCW hinterp i

end SeedRetainedPair

end ContinuousFlexibility.Radial
