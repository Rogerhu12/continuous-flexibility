import ContinuousFlexibility.Radial.InnerSelectedWeightedModels
import ContinuousFlexibility.Radial.InnerActualReferenceBlocks

/-!
# The two interface estimates for one selected physical inner chain

The reference keeps every complete positive-gap flux block. Local
model estimates yield both signed normalized error bounds and both
physical Poisson bounds. Invertibility is established at weight
exponent zero, so the same interface inverse is used for every later
weight exponent and sign.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

/-- This constant depends only on the selected geometry, and not on
the band, the even mode, or the weight exponent. -/
def poissonConstant : ℝ :=
  max (2 * innerSelectedModelPoissonConstant) (Real.sqrt (12 / P.gapSlope))

theorem poissonConstant_pos : 0 < P.poissonConstant :=
  (mul_pos (by norm_num) innerSelectedModelPoissonConstant_pos).trans_le (le_max_left _ _)

variable {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))

local notation "A" => P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
local notation "models" => P.models hCentralFamily hMorseFamily hX hsupport K q hq hband

theorem actualChain_reference_posDef : (A).referenceMatrix.PosDef :=
  (A).referenceMatrix_posDef P.geometry.2.2.1.1
    (P.actualChain_kappa_pos hCentralFamily hMorseFamily hX hsupport K q hq hband)

theorem actualChain_diagonal_le_reference :
    Matrix.diagonal (A).kappa ≤ (A).referenceMatrix :=
  (A).diagonal_le_referenceMatrix P.geometry.2.2.1.1

/-- The full reference vanishes between different gap blocks. Each
fiber has at most two cut variables by innerModelChainGapOfCut_card_le_two. -/
theorem actualChain_reference_blocks (i k : Fin (2 * (2 * K + 1)))
    (hik : innerModelChainGapOfCut i ≠ innerModelChainGapOfCut k) :
    (A).referenceMatrix i k = 0 :=
  innerActualChainOfModelsAndGaps_reference_blocks (P.chain K) (decide (q = 1))
    ((2 : ℝ) * q) (innerMorseInnerCenter K) (P.centralColumn q hsupport)
    models _ i k hik

/-- Both cuts of each genuine gap have the same actual weight. -/
theorem actualChain_reference_commute (γ : ℝ) :
    Commute (Matrix.diagonal (innerMorseInnerInterfaceWeight S.chain.index K a γ))
      (A).referenceMatrix :=
  innerMorseInnerActual_reference_commute S.chain.index K a γ (P.chain K) models _

/-- The strict one-half estimate is proved from the selected local
models for both signs, on one and the same full matrix. -/
theorem actualChain_normalized_error (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool) :
    ‖innerInterfaceWeightedError (A).referenceMatrix
      (innerInterfaceWeight
        (Matrix.diagonal (innerMorseInnerInterfaceWeight S.chain.index K a γ)) sign)
      (A).errorMatrix‖ < 1 / 2 :=
  innerMorseInnerActual_normalized_error S.chain.index K a γ (P.chain K) models _
    P.geometry.2.2.1.1
    (P.models_kappa_pos hCentralFamily hMorseFamily hX hsupport K q hq hband)
    hη hηsmall
    (P.models_error_le hCentralFamily hMorseFamily hX hsupport K q hq hband hγ) sign

/-- Weight exponent zero proves invertibility once. No weight exponent
or sign is an input to this proof or to the selected inverse. -/
theorem actualChain_flux_isUnit (hη : 0 ≤ η) (hηsmall : η < 1 / 4) :
    IsUnit (A).fluxMatrix :=
  innerMorseInnerActual_flux_isUnit S.chain.index K a 0 (P.chain K) models _
    P.geometry.2.2.1.1
    (P.models_kappa_pos hCentralFamily hMorseFamily hX hsupport K q hq hband)
    hη hηsmall
    (P.models_error_le hCentralFamily hMorseFamily hX hsupport K q hq hband
      (by norm_num : |(0 : ℝ)| ≤ 1))

/-- The physical Poisson estimate has a single geometry-dependent
constant and is uniform over all retained cells and all positive
even modes in their actual bands. -/
theorem actualChain_poisson_bound
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index)
    (hNa : 64 * a ≤ (S.chain.index : ℝ)) (hCM : 0 < CM)
    {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool) :
    ‖innerWeightedPoisson
      (innerMorseInnerSupportedWeightEquiv S.chain.index K a γ (P.chain K) A)
      (innerMorseInnerInterfaceEquiv S.chain.index K a γ)
      ((A).poisson P.geometry.2.2.1.1)
      (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
        (innerInterfaceInverseSqrt (A).referenceMatrix)) sign‖ ≤
      P.poissonConstant / ((2 : ℝ) * q) := by
  let CW := innerMorseInnerWeightBound S.chain.index K a γ (P.chain K) A
  have hj : 0 < (2 : ℝ) * q := by
    exact_mod_cast (show 0 < 2 * q by omega)
  have h := innerMorseInnerActual_poisson_bound S.chain.index K a γ (P.chain K) models
    (P.gapChart K ((2 : ℝ) * q) hj)
    P.geometry.2.2.1.1
    (P.models_kappa_pos hCentralFamily hMorseFamily hX hsupport K q hq hband)
    CW CW
    (innerMorseInnerWeight_abs_le S.chain.index K a γ (P.chain K) A)
    (innerMorseInnerWeight_inv_abs_le S.chain.index K a γ (P.chain K) A)
    innerSelectedModelPoissonConstant_pos.le P.gapSlope_pos hj
    (fun _ => le_rfl)
    (fun sign p i => by
      simpa only [ite_self] using
        P.models_column_norm_le hCentralFamily hMorseFamily hX hsupport K q hq hband
          ha hN hNa hCM γ hγ sign CW
          (innerMorseInnerSignedWeight_abs_le S.chain.index K a γ (P.chain K) A sign) p i)
    sign
  simpa only [innerMorseInnerSupportedWeightEquiv, innerMorseInnerInterfaceEquiv,
    poissonConstant, CW, actualChain] using h

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
