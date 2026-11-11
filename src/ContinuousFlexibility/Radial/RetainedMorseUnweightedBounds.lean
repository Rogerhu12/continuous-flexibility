import ContinuousFlexibility.Radial.RetainedMorsePoissonBound
import ContinuousFlexibility.Radial.InnerModelEndpointEnergy
import ContinuousFlexibility.Radial.InnerMorseWeights

/-!
# Constant-weight estimates for the same retained Morse charts

The final frozen regional statement uses the original radial measure.
At exponent zero every prescribed cut weight is exactly one. The local
model selected before the reference is built therefore supplies its
actual physical error and its normalized column bound without a new
choice of model or a condition number.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

theorem innerMorseCutWeight_unweighted (N m : ℕ) (side : Bool) :
    innerMorseCutWeight N 0 0 side m = fun _ => 1 := by
  funext i
  simp [innerMorseCutWeight, innerMorseInwardWeight, innerMorseOutwardWeight,
    innerCellWeight, innerGeometricMeanWeight]

theorem retained_radialE_power_le {m n : ℕ} (hmn : m ≤ n) :
    radialE m ^ (36 : ℝ) ≤ radialE n ^ (37 : ℝ) := by
  have hE : radialE m ≤ radialE n := exp_le_exp.mpr (radialQ_monotone hmn)
  have h1 : 1 ≤ radialE n := one_le_exp.mpr (radialQ_nonneg n)
  have hp := pow_le_pow_left₀ (exp_pos (radialQ m)).le hE 36
  have hs : radialE n ^ 36 ≤ radialE n ^ 37 := by
    calc
      _ = radialE n ^ 36 * 1 := (mul_one _).symm
      _ ≤ radialE n ^ 36 * radialE n :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (exp_pos _).le _)
      _ = _ := (pow_succ _ _).symm
  simpa only [rpow_ofNat] using hp.trans hs

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

theorem retainedMorseModelChart_unweighted_poisson_bound (hj : 1 ≤ j) (hC : 0 < Cmodel)
    (hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / j) (i : Fin 2) :
    ‖(sqrt (A.kappa i))⁻¹ • A.column i‖ ≤ innerMorsePoissonConstant / j :=
  P.retainedMorseModelChart_column_bound hw hS G₀ hband H bordered j central piece column
    side m hm haway hleft hright hB M hj hC hrem i

theorem retainedMorseModelChart_unweighted_error_bound {η : ℝ}
    (herror : ∀ height : ℝ, 0 < height → ∀ sign : Bool,
      ‖innerTwoCutWeightedError
        (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
        (innerMorseCutWeight S.chain.index 0 0 side m)
        (M.physicalFluxError height (fun _ => 1)) sign‖ ≤ η)
    (sign : Bool) :
    ‖innerTwoCutWeightedError A.kappa (fun _ => 1) A.errorMatrix sign‖ ≤ η := by
  have hkappa : A.kappa = innerPhysicalCutKappa
      (P.sideHeight side * morseChainAmplitude S.chain S.sigma m)
      (fun _ => 1) (fun i => (M.column i).inwardEnergy) := by
    funext i
    rw [retainedMorseModelChart_kappa]
    simp only [innerPhysicalCutKappa, one_pow, mul_one]
  rw [hkappa, retainedMorseModelChart_errorMatrix]
  simpa only [innerMorseCutWeight_unweighted] using
    herror (P.sideHeight side * morseChainAmplitude S.chain S.sigma m)
      (mul_pos (P.sideHeight_pos side)
        (innerMorseChain_height_pos (hS.2.2.2.1 S.sigma hS.2.2.1).1 side hm)) sign

theorem retainedMorseModelChart_dirichlet_cost_at_upper {upper : ℕ}
    (hj : 1 ≤ j) (hC : 0 ≤ Cmodel) (hupper : m ≤ upper) :
    ‖A.dirichlet‖ ≤ innerMorseDirichletConstant Cmodel * radialE upper ^ (37 : ℝ) :=
  (P.retainedMorseModelChart_dirichlet_cost hw hS G₀ hband H bordered j central piece column
    side m hm haway hleft hright hB M hj hC).trans
    (mul_le_mul_of_nonneg_left (retained_radialE_power_le hupper)
      (innerMorseDirichletConstant_nonneg hC))

end SeedRetainedPair

end ContinuousFlexibility.Radial
