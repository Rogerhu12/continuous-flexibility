module

public import ContinuousFlexibility.Radial.MatchedInnerModelWeights
public import ContinuousFlexibility.Radial.InnerMorseInnerWeightCosts
public import ContinuousFlexibility.Radial.InnerCoefficientCosts

/-!
# Physical gap and middle data for the original finite-chain weight

The weight is the original interpolation on the actual chain. On a gap
it and both incident cut weights have the same value. On the middle
model it preserves the original full Poisson column, including its
scalar component. The fixed coefficient loss absorbs the unweighted
Dirichlet cost of every actual piece with one exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section GapAndMiddle

variable {D : ReferenceData} (N K : ℕ) (a γ σ : ℝ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ)

/-- A gap has the same positive physical and interface weight for
either real power. No lower bound for its slope enters this identity. -/
theorem matchedInner_signed_gap_weight (g : Fin (2 * K + 2)) :
    ∃ c : ℝ, 0 < c ∧
      EqOn (fun x => (innerMorseInnerWeight N K a γ G l r x) ^ σ)
        (fun _ => c) (Ioo (G.left (innerModelChainGap g)) (G.right (innerModelChainGap g))) ∧
      (0 < (innerModelChainGap g).val →
        innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainGap g)
          (fun i => (innerMorseInnerInterfaceWeight N K a γ i) ^ σ) 1 0 = c) ∧
      ((innerModelChainGap g).val < 2 * (2 * K + 1) →
        innerChainScalarRestriction (2 * (2 * K + 1)) (innerModelChainGap g)
          (fun i => (innerMorseInnerInterfaceWeight N K a γ i) ^ σ) 1 1 = c) := by
  refine ⟨(innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ^ σ,
    rpow_pos_of_pos (innerMorseInnerCutWeight_pos N K a γ _) σ, ?_, ?_, ?_⟩
  · intro x hx
    change (innerMorseInnerWeight N K a γ G l r x) ^ σ =
      (innerMorseInnerCutWeight N K a γ (innerModelChainGap g).succ) ^ σ
    rw [innerMorseInnerWeight_on_gap N K a γ G l r g ⟨hx.1, hx.2.le⟩]
  · intro hp
    simpa only [innerMorseInnerInterfaceWeight, innerMorseInnerCutWeight_gap] using
      innerChainScalarRestriction_full_left (2 * (2 * K + 1)) (innerModelChainGap g)
        (fun i => (innerMorseInnerCutWeight N K a γ i) ^ σ) hp
  · intro hp
    exact innerChainScalarRestriction_full_right (2 * (2 * K + 1)) (innerModelChainGap g)
      (fun i => (innerMorseInnerCutWeight N K a γ i) ^ σ) hp

/-- The middle model sees exactly the unweighted normalized column.
The original scalar component is unchanged by the field multiplier. -/
theorem matchedInner_central_weighted_column_norm
    {bordered : Bool} {j : ℝ} {column : RadialModeL2 D}
    (M : InnerRadialModelChart D G bordered j
      (innerModelChainPiece (innerMorseInnerCenter K)) column
      (innerModelChainPiece (innerMorseInnerCenter K)))
    (CW : ℝ) (hCW : ∀ x, |(innerMorseInnerWeight N K a γ G l r x) ^ σ| ≤ CW)
    (i : Fin 2) :
    ‖(innerChainScalarRestriction (2 * (2 * K + 1))
        (innerModelChainPiece (innerMorseInnerCenter K))
        (fun k => (innerMorseInnerInterfaceWeight N K a γ k) ^ σ) 1 i *
        sqrt (M.kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D)
          (fun x => (innerMorseInnerWeight N K a γ G l r x) ^ σ)
          ((innerMorseInnerWeight_measurable N K a γ G l r).pow_const σ) CW hCW)
        (M.column i)‖ =
      ‖(sqrt (M.kappa i))⁻¹ • M.column i‖ := by
  have hcut :
      innerChainScalarRestriction (2 * (2 * K + 1))
        (innerModelChainPiece (innerMorseInnerCenter K))
        (fun k => (innerMorseInnerInterfaceWeight N K a γ k) ^ σ) 1 i = 1 := by
    simpa only [one_rpow, innerMorseInnerInterfaceWeight_model,
      innerMorseInnerModelWeight_center] using
      innerChainScalarRestriction_map (2 * (2 * K + 1))
        (innerModelChainPiece (innerMorseInnerCenter K))
        (innerMorseInnerInterfaceWeight N K a γ) 1 (fun z : ℝ => z ^ σ) i
  rw [hcut, one_mul, M.matchedColumn_weight_one
    (fun x => (innerMorseInnerWeight N K a γ G l r x) ^ σ)
    ((innerMorseInnerWeight_measurable N K a γ G l r).pow_const σ) CW hCW]
  intro x hx
  change (innerMorseInnerWeight N K a γ G l r x) ^ σ = 1
  rw [innerMorseInnerWeight_on_center N K a γ G l r ⟨hx.1, hx.2.le⟩, one_rpow]

end GapAndMiddle

namespace InnerRadialActualChain

variable {D : ReferenceData} {N K : ℕ}
  {G : InnerRadialChainGeometry D (2 * (2 * K + 1))}
  {bordered : Bool} {j : ℝ} {central : Fin (2 * (2 * K + 1) + 1)}
  {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- The actual unweighted piece cost has the fixed exponent 36.
The square-root coefficient ratios and the original loss 37 give
a bound independent of the retained length and the frequency. -/
theorem matched_piece_dirichlet_fixed37
    (hw : ContDiff ℝ ∞ D.w) {KD : ℝ} (hKD : 0 ≤ KD)
    (hcost : ∀ p, ‖(C.piece p).dirichlet hw‖ ≤
      KD * radialE (innerMorseInnerPieceIndex N K p) ^ (36 : ℝ))
    (p : Fin (2 * (2 * K + 1) + 1)) :
    innerCoefficientLoss N 37 (innerMorseInnerPieceIndex N K p) *
      ((sqrt (radialE (innerMorseInnerPieceIndex N K p))) ^ 2 *
        ‖(C.piece p).dirichlet hw‖) ≤ KD * radialE N ^ (37 : ℝ) := by
  simpa only [show (36 : ℝ) + 1 = 37 by norm_num] using
    inner_dirichlet_fixed_loss_cost (p := (36 : ℝ)) (ℓ := (37 : ℝ))
      hKD (sqrt_nonneg _) (norm_nonneg _) (le_refl _) (hcost p)
      (innerMorseInnerPieceIndex_bounds N K p).1 (by norm_num)

end InnerRadialActualChain

end ContinuousFlexibility.Radial
