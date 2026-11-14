module

public import ContinuousFlexibility.Radial.RetainedMorseModelChart
public import ContinuousFlexibility.Radial.InnerMorseScaledPhysicalPoisson

/-!
# Signed weights on the actual retained Morse pieces

The retained chart has the same original localized model and the same
positive radius and height dilations as the scaled physical chart.
The original normalized remainder therefore controls its actual
weighted physical columns. Its conormal error is the error of that
same model at the retained physical height.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G₀ : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  {n : ℕ} (H : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : S.chain.index ≤ m) (haway : piece ≠ central)
  (hleft : H.left piece = P.sideRadius side * innerMorseChainCut S.chain side m 0)
  (hright : H.right piece = P.sideRadius side * innerMorseChainCut S.chain side m 1)
  {Cmodel Kmodel : ℝ}
  (hB : BufferHypotheses
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)) Cmodel Kmodel)

local notation "A" => P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
  side m hm haway hleft hright hB M

/-- The true retained chart inherits the frequency estimate for both
reciprocal weight signs, directly from the original selected remainder. -/
theorem retainedMorseModelChart_weighted_column_bound
    (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    (hmN : N ≤ m) (hj : 1 ≤ j) (hC : 0 < Cmodel)
    (hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / j)
    (γ sign : ℝ) (hγ : |γ| ≤ 1) (hsign : |sign| ≤ 1)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (hinterp : ∀ x ∈ Icc innerMorseBufferLeftCut
        (innerMorseBufferRightCut (morseChainA S.chain m) (morseChainB S.chain m)),
      W (P.sideRadius side * S.chain.radius side m x) =
        (innerMorseInterpolatedWeight N a γ side m
          (P.sideRadius side * S.chain.radius side m (bufferInnerWall
            (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) j
              (8 * (S.chain.d m : ℝ) ^ 9)) 0))
          (P.sideRadius side * S.chain.radius side m (bufferInnerWall
            (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m) j
              (8 * (S.chain.d m : ℝ) ^ 9)) 1))
          (P.sideRadius side * S.chain.radius side m x)) ^ sign)
    (i : Fin 2) :
    ‖((innerMorseCutWeight N a γ side m i) ^ sign * sqrt ((A).kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) ((A).column i)‖ ≤
          innerMorsePoissonConstant / j := by
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hindex : 10 ≤ S.chain.index := (by norm_num : 10 ≤ 100).trans G₀.start_large
  have hprofile (x : ℝ) (hx : x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA S.chain m) (morseChainB S.chain m))) :
      D.w (P.sideRadius side * S.chain.radius side m x) =
        P.sideHeight side * P.sideRadius side * (S.family S.sigma).w
          (S.chain.radius side m x) := by
    have hp := selected_morseCell_retained hS G₀ hband side hm
      (innerMorseChain_buffer_subset hreal side hm hx)
    exact P.reference_side_old_value hw hS side hp.1 hp.2
  have hb := innerMorseScaledPhysicalModelChart_poisson_bound hreal hindex
    D H bordered j central piece column side m hm (P.sideRadius side) (P.sideHeight side)
    (P.sideRadius_pos side) (P.sideHeight_pos side) hprofile haway hleft hright hB M
    N ha hN hNa hmN hj hC hrem γ sign hγ hsign W hW CW hWC hinterp i
  simpa only [innerMorseScaledPhysicalModelChart, retainedMorseModelChart] using hb

/-- The actual retained conormal matrix is the original model's
physical error at its retained height. The same raw model bound
therefore controls either sign of the true cut weights. -/
theorem retainedMorseModelChart_weighted_error_bound
    (N : ℕ) (a γ η : ℝ)
    (herror : ∀ height : ℝ, 0 < height → ∀ sign : Bool,
      ‖innerTwoCutWeightedError
        (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
        (innerMorseCutWeight N a γ side m)
        (M.physicalFluxError height (fun _ => 1)) sign‖ ≤ η)
    (sign : Bool) :
    ‖innerTwoCutWeightedError (A).kappa (innerMorseCutWeight N a γ side m)
      (A).errorMatrix sign‖ ≤ η := by
  have hkappa : (A).kappa = innerPhysicalCutKappa
      (P.sideHeight side * morseChainAmplitude S.chain S.sigma m)
      (fun _ => 1) (fun i => (M.column i).inwardEnergy) := by
    funext i
    rw [retainedMorseModelChart_kappa]
    simp only [innerPhysicalCutKappa, one_pow, mul_one]
  rw [hkappa, retainedMorseModelChart_errorMatrix]
  exact herror (P.sideHeight side * morseChainAmplitude S.chain S.sigma m)
    (mul_pos (P.sideHeight_pos side)
      (innerMorseChain_height_pos (hS.2.2.2.1 S.sigma hS.2.2.1).1 side hm)) sign

end SeedRetainedPair

end ContinuousFlexibility.Radial
