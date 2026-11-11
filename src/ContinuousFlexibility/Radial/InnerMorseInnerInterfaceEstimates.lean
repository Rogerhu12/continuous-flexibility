import ContinuousFlexibility.Radial.InnerMorseInnerWeightInterfaces
import ContinuousFlexibility.Radial.InnerRadialInterfaceWeights

/-!
# Actual weighted interface estimates for the alternating inner chain

The physical multiplier and cut diagonal are determined by the same
actual dictionary. The local model errors and columns are the only
analytic inputs here. Every gap-weight condition follows from the
actual finite-chain weights, so neither global smallness nor a global
Poisson estimate is an assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

section ActualModels

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  {bordered : Bool} {j : ℝ} {column : RadialModeL2 D}
  (models : ∀ p : Fin (2 * K + 1), InnerRadialModelChart D G bordered j
    (innerModelChainPiece (innerMorseInnerCenter K)) column (innerModelChainPiece p))
  (gaps : ∀ g : Fin (2 * K + 2), InnerRadialGapChart D G j
    (innerModelChainPiece (innerMorseInnerCenter K)) (innerModelChainGap g))

local notation "A" => innerActualChainOfModelsAndGaps G bordered j
  (innerMorseInnerCenter K) column models gaps
local notation "W" => innerMorseInnerWeight N K a γ G (InnerRadialActualChain.leftWall A) (InnerRadialActualChain.rightWall A)
local notation "w" => innerMorseInnerInterfaceWeight N K a γ

/-- A gap's genuine common cut weight is also its spatial weight.
The same assertion handles internal and terminal gaps. -/
theorem innerMorseInnerActual_gap_weight_data
    (p : Fin (2 * (2 * K + 1) + 1))
    (Q : InnerRadialGapChart D G j (innerModelChainPiece (innerMorseInnerCenter K)) p)
    (hp : (A).piece p = Sum.inr Q) :
    ∃ c : ℝ, 0 < c ∧ EqOn W (fun _ => c) (Ioo (G.left p) (G.right p)) ∧
      (0 < p.val → innerChainScalarRestriction (2 * (2 * K + 1)) p w 1 0 = c) ∧
      (p.val < 2 * (2 * K + 1) →
        innerChainScalarRestriction (2 * (2 * K + 1)) p w 1 1 = c) := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerActualChainOfModelsAndGaps_model] at hp
    cases hp
  · exact ⟨innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ,
      innerMorseInnerWeight_actual_gap_data N K a γ G A g⟩

/-- The full reference commutes with the actual cut diagonal. -/
theorem innerMorseInnerActual_reference_commute :
    Commute (Matrix.diagonal w) (A).referenceMatrix := by
  apply (A).referenceMatrix_commute w
  intro p Q hp
  obtain ⟨c, _, _, hleft, hright⟩ :=
    innerMorseInnerActual_gap_weight_data N K a γ G models gaps p Q hp
  exact ⟨c, hleft, hright⟩

/-- Local errors use exactly the cut weights of their own model slots. -/
theorem innerMorseInnerActual_model_error {η : ℝ}
    (herror : ∀ p sign,
      ‖innerTwoCutWeightedError (models p).kappa
        (innerMorseInnerModelWeight N K a γ p) (models p).errorMatrix sign‖ ≤ η)
    (p : Fin (2 * (2 * K + 1) + 1))
    (M : InnerRadialModelChart D G bordered j
      (innerModelChainPiece (innerMorseInnerCenter K)) column p)
    (hp : (A).piece p = Sum.inl M) (sign : Bool) :
    ‖innerTwoCutWeightedError M.kappa
      (innerChainScalarRestriction (2 * (2 * K + 1)) p w 1) M.errorMatrix sign‖ ≤ η := by
  rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
  · rw [innerActualChainOfModelsAndGaps_model] at hp
    have he : models q = M := Sum.inl.inj hp
    subst M
    have hw : innerChainScalarRestriction (2 * (2 * K + 1))
        (innerModelChainPiece q) w 1 = innerMorseInnerModelWeight N K a γ q :=
      funext (innerMorseInnerInterfaceWeight_model N K a γ q)
    rw [hw]
    exact herror q sign
  · rw [innerActualChainOfModelsAndGaps_gap] at hp
    cases hp

/-- Uniform local model errors imply the strict one-half bound for
either conjugation of the same full interface matrix. -/
theorem innerMorseInnerActual_normalized_error (hDw : ContDiff ℝ ∞ D.w)
    (hκ : ∀ p i, 0 < (models p).kappa i) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (herror : ∀ p sign,
      ‖innerTwoCutWeightedError (models p).kappa
        (innerMorseInnerModelWeight N K a γ p) (models p).errorMatrix sign‖ ≤ η)
    (sign : Bool) :
    ‖innerInterfaceWeightedError (A).referenceMatrix
      (innerInterfaceWeight (Matrix.diagonal w) sign) (A).errorMatrix‖ < 1 / 2 :=
  (A).normalized_error_both hDw
    (innerActualChainOfModelsAndGaps_kappa_pos G bordered j
      (innerMorseInnerCenter K) column models gaps hκ)
    w (innerMorseInnerInterfaceWeight_pos N K a γ)
    (innerActualChainOfModelsAndGaps_kappa_separated G bordered j
      (innerMorseInnerCenter K) column models gaps)
    (innerActualChainOfModelsAndGaps_model_internal G bordered j
      (innerMorseInnerCenter K) column models gaps hκ)
    hη hηsmall
    (innerMorseInnerActual_model_error N K a γ G models gaps herror) sign

/-- Invertibility of the actual total flux follows from the local
models and genuine gap weights, without an interface hypothesis. -/
theorem innerMorseInnerActual_flux_isUnit (hDw : ContDiff ℝ ∞ D.w)
    (hκ : ∀ p i, 0 < (models p).kappa i) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (herror : ∀ p sign,
      ‖innerTwoCutWeightedError (models p).kappa
        (innerMorseInnerModelWeight N K a γ p) (models p).errorMatrix sign‖ ≤ η) :
    IsUnit (A).fluxMatrix :=
  (A).fluxMatrix_isUnit hDw
    (innerActualChainOfModelsAndGaps_kappa_pos G bordered j
      (innerMorseInnerCenter K) column models gaps hκ)
    (Matrix.diagonal w)
    (Matrix.posDef_diagonal_iff.mpr (innerMorseInnerInterfaceWeight_pos N K a γ))
    (innerMorseInnerActual_reference_commute N K a γ G models gaps)
    (innerMorseInnerActual_normalized_error N K a γ G models gaps hDw hκ hη hηsmall herror)

/-- The actual normalized columns and the geometric gap slope give
both signed estimates, with no factor depending on the number of cells. -/
theorem innerMorseInnerActual_poisson_bound (hDw : ContDiff ℝ ∞ D.w)
    (hκ : ∀ p i, 0 < (models p).kappa i)
    (CW Cinv : ℝ) (hWC : ∀ x, |W x| ≤ CW) (hWinv : ∀ x, |(W x)⁻¹| ≤ Cinv)
    {CM s : ℝ} (hCM : 0 ≤ CM) (hs : 0 < s) (hj : 0 < j)
    (hslope : ∀ g, s ≤ (gaps g).slope)
    (hcolumns : ∀ sign : Bool, ∀ p i,
      ‖(innerSignedWeight (innerMorseInnerModelWeight N K a γ p) sign i *
          Real.sqrt ((models p).kappa i))⁻¹ •
        innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) (innerSignedWeight W sign)
            (innerSignedWeight_measurable W
              (innerMorseInnerWeight_measurable N K a γ G (A).leftWall (A).rightWall) sign)
            (if sign then CW else Cinv)
            (innerSignedWeight_abs_le W CW Cinv hWC hWinv sign)) ((models p).column i)‖ ≤ CM / j)
    (sign : Bool) :
    ‖innerWeightedPoisson
      (innerSupportedWeightEquiv (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
        W (innerMorseInnerWeight_measurable N K a γ G (A).leftWall (A).rightWall)
        (innerMorseInnerWeight_pos N K a γ G (A).leftWall (A).rightWall)
        CW Cinv hWC hWinv)
      (innerMatrixEquiv (Matrix.diagonal w)
        (Matrix.PosDef.isUnit
          (Matrix.posDef_diagonal_iff.mpr (innerMorseInnerInterfaceWeight_pos N K a γ))))
      ((A).poisson hDw)
      (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ)
        (innerInterfaceInverseSqrt (A).referenceMatrix)) sign‖ ≤
      max (2 * CM) (Real.sqrt (12 / s)) / j := by
  apply (A).weighted_poisson_both_signs hDw W
    (innerMorseInnerWeight_measurable N K a γ G (A).leftWall (A).rightWall)
    (innerMorseInnerWeight_pos N K a γ G (A).leftWall (A).rightWall)
    CW Cinv hWC hWinv w (innerMorseInnerInterfaceWeight_pos N K a γ)
    hCM hs hj
    (innerActualChainOfModelsAndGaps_kappa_pos G bordered j
      (innerMorseInnerCenter K) column models gaps hκ)
  · intro p M hp
    exact (innerActualChainOfModelsAndGaps_model_internal G bordered j
      (innerMorseInnerCenter K) column models gaps hκ p M hp).2.2
  · intro sign p M hp i
    rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
    · rw [innerActualChainOfModelsAndGaps_model] at hp
      have he : models q = M := Sum.inl.inj hp
      subst M
      simpa only [innerMorseInnerInterfaceWeight_signed_model] using hcolumns sign q i
    · rw [innerActualChainOfModelsAndGaps_gap] at hp
      cases hp
  · intro p Q hp
    obtain ⟨c, hc, hconstant, hleft, hright⟩ :=
      innerMorseInnerActual_gap_weight_data N K a γ G models gaps p Q hp
    refine ⟨?_, c, hc, hconstant, hleft, hright⟩
    rcases innerModelChainPiece_or_gap p with ⟨q, rfl⟩ | ⟨g, rfl⟩
    · rw [innerActualChainOfModelsAndGaps_model] at hp
      cases hp
    · rw [innerActualChainOfModelsAndGaps_gap] at hp
      have he : gaps g = Q := Sum.inr.inj hp
      subst Q
      exact hslope g

end ActualModels

end ContinuousFlexibility.Radial
