import ContinuousFlexibility.Radial.MatchedInnerFiniteWeightData
import ContinuousFlexibility.Radial.MatchedInnerHardyWeightedInverse

/-!
# The original finite-chain inverse with its fixed coefficient loss

Both reciprocal physical weights are the original finite-chain
interpolation. The gap constancy, local weight ratios and coefficient
loss are proved from that interpolation. The only quantitative inputs
are the actual model columns and errors, actual endpoint energy, and
unweighted piece Dirichlet costs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

namespace InnerRadialActualChain

variable {D : ReferenceData} (N K : ℕ)
  (G : InnerRadialChainGeometry D (2 * (2 * K + 1)))
  {bordered : Bool} {j : ℝ} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j
    (innerModelChainPiece (innerMorseInnerCenter K)) column)
  (l r : Fin (2 * (2 * K + 1) + 1) → ℝ) (a γ : ℝ)
  (CW : ℝ)

local notation "σ" => fun sign : Bool => if sign then (1 : ℝ) else -1
local notation "W" => fun sign x =>
  (innerMorseInnerWeight N K a γ G l r x) ^ (σ sign)
local notation "w" => fun sign i =>
  (innerMorseInnerInterfaceWeight N K a γ i) ^ (σ sign)
local notation "loss" => innerMorseInnerLoss N K G 37
local notation "hW" => fun sign =>
  (innerMorseInnerWeight_measurable N K a γ G l r).pow_const (σ sign)
local notation "hloss" => innerMorseInnerLoss_measurable N K G 37
local notation "hlossBound" => innerMorseInnerLoss_le_one N K G (by norm_num : (0 : ℝ) ≤ 37)

variable (hCW : ∀ sign x, |W sign x| ≤ CW)

local notation "U" => fun sign =>
  innerSupportedWeightMultiplier (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (fun x => loss x * W sign x) (hloss.mul (hW sign)) CW
    (innerWeight_mul_bound_one loss (W sign) hlossBound CW (hCW sign))
local notation "V" => fun sign =>
  innerSupportedWeightMultiplier (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (W sign) (hW sign) CW (hCW sign)

/-- The same original inverse has both signed bounds with loss 37.
All constants on the right are independent of the retained length;
the frequency occurs only in the actual normalized model term. -/
theorem inverse_morse_weighted_fixed_loss
    (hw : ContDiff ℝ ∞ D.w)
    (ha : 0 ≤ a) (hγ : |γ| ≤ 1) (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    (hκ : ∀ i, 0 < C.kappa i)
    (hsep : ∀ i : Fin (2 * (2 * K + 1)),
      (C.piece i.castSucc).kappa 1 = 0 ∨ (C.piece i.succ).kappa 0 = 0)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j
        (innerModelChainPiece (innerMorseInnerCenter K)) column p),
      C.piece p = .inl M →
        0 < p.val ∧ p.val < 2 * (2 * K + 1) ∧ ∀ i, 0 < M.kappa i)
    (hgapShape : ∀ p (Q : InnerRadialGapChart D G j
        (innerModelChainPiece (innerMorseInnerCenter K)) p),
      C.piece p = .inr Q → ∃ g : Fin (2 * K + 2), p = innerModelChainGap g)
    {η KP CE KD : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (hKP : 0 ≤ KP) (hCE : 0 ≤ CE) (hKD : 0 ≤ KD) (hj : 0 < j)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2)
    (herror : ∀ p (M : InnerRadialModelChart D G bordered j
        (innerModelChainPiece (innerMorseInnerCenter K)) column p),
      C.piece p = .inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa
          (innerChainScalarRestriction (2 * (2 * K + 1)) p
            (innerMorseInnerInterfaceWeight N K a γ) 1) M.errorMatrix sign‖ ≤ η)
    (hcolumns : ∀ sign p (M : InnerRadialModelChart D G bordered j
        (innerModelChainPiece (innerMorseInnerCenter K)) column p),
      C.piece p = .inl M → ∀ i,
        ‖(innerChainScalarRestriction (2 * (2 * K + 1)) p (w sign) 1 i *
            sqrt (M.kappa i))⁻¹ •
          innerBorderFieldMap (radialHilbertMeasure D)
            (innerWeightMultiplier (radialHilbertMeasure D) (W sign)
              (hW sign) CW (hCW sign)) (M.column i)‖ ≤ KP / j)
    (hendpoints : ∀ (i : Fin (2 * (2 * K + 1)))
        (Q : InnerRadialGapChart D G j
          (innerModelChainPiece (innerMorseInnerCenter K)) i.succ),
      C.piece i.succ = .inr Q →
        D.w (G.left i.succ) / G.left i.succ ≤ CE * C.kappa i)
    (hcost : ∀ p, ‖(C.piece p).dirichlet hw‖ ≤
      KD * radialE (innerMorseInnerPieceIndex N K p) ^ (36 : ℝ)) :
    ∃ hS : IsUnit C.fluxMatrix, ∀ sign : Bool,
      ‖U sign ∘L C.inverse hw hS ∘L V (!sign)‖ ≤
        KD * radialE N ^ (37 : ℝ) +
          2 * (max ((2 * KP / j) ^ 2) 48 + 24 * CE) := by
  have hpos : ∀ sign x, 0 < W sign x :=
    fun sign x => rpow_pos_of_pos (innerMorseInnerWeight_pos N K a γ G l r x) (σ sign)
  have hInv : ∀ x, W false x = (W true x)⁻¹ := by
    intro x
    simp only [Bool.false_eq_true, ite_false, ite_true, rpow_neg_one, rpow_one]
  have hopp : ∀ sign x, W (!sign) x = (W sign x)⁻¹ := by
    intro sign x
    cases sign <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
        rpow_neg_one, rpow_one, inv_inv]
  have hwpos : ∀ sign i, 0 < w sign i := fun sign i =>
    rpow_pos_of_pos (innerMorseInnerInterfaceWeight_pos N K a γ i) (σ sign)
  have hwInv : ∀ i, w false i = (w true i)⁻¹ := by
    intro i
    simp only [Bool.false_eq_true, ite_false, ite_true, rpow_neg_one, rpow_one]
  have hσ : ∀ sign, |σ sign| ≤ 1 := by
    intro sign
    cases sign <;> norm_num
  have hgapData : ∀ sign p (Q : InnerRadialGapChart D G j
        (innerModelChainPiece (innerMorseInnerCenter K)) p),
      C.piece p = .inr Q →
        ∃ c : ℝ, 0 < c ∧ EqOn (W sign) (fun _ => c) (Ioo (G.left p) (G.right p)) ∧
          (0 < p.val → innerChainScalarRestriction (2 * (2 * K + 1)) p (w sign) 1 0 = c) ∧
          (p.val < 2 * (2 * K + 1) →
            innerChainScalarRestriction (2 * (2 * K + 1)) p (w sign) 1 1 = c) := by
    intro sign p Q hp
    obtain ⟨g, hg⟩ := hgapShape p Q hp
    subst p
    exact matchedInner_signed_gap_weight N K a γ (σ sign) G l r g
  let lossCost := fun p => innerCoefficientLoss N 37 (innerMorseInnerPieceIndex N K p)
  let ratio := fun (_ : Bool) p => sqrt (radialE (innerMorseInnerPieceIndex N K p))
  let base := fun sign => innerMorseInnerPieceBase N K a γ (σ sign)
  have hcenterLoss : lossCost (innerModelChainPiece (innerMorseInnerCenter K)) = 1 := by
    dsimp only [lossCost]
    rw [innerMorseInnerPieceIndex_model, innerMorseInnerModelIndex_center,
      innerCoefficientLoss, div_self (exp_pos (radialQ N)).ne', one_rpow]
  have hcenterW : ∀ sign, 1 ≤
      lossCost (innerModelChainPiece (innerMorseInnerCenter K)) *
        ratio sign (innerModelChainPiece (innerMorseInnerCenter K)) *
        base sign (innerModelChainPiece (innerMorseInnerCenter K)) := by
    intro sign
    rw [hcenterLoss]
    simpa only [ratio, base, innerMorseInnerPieceIndex_model,
      innerMorseInnerModelIndex_center, innerMorseInnerPieceBase_center,
      one_mul, mul_one] using inner_radialE_sqrt_ge_one N
  have hcenterV : ∀ sign, 1 ≤
      ratio sign (innerModelChainPiece (innerMorseInnerCenter K)) /
        base sign (innerModelChainPiece (innerMorseInnerCenter K)) := by
    intro sign
    simpa only [ratio, base, innerMorseInnerPieceIndex_model,
      innerMorseInnerModelIndex_center, innerMorseInnerPieceBase_center,
      div_one] using inner_radialE_sqrt_ge_one N
  have hlocalW : ∀ sign p x, x ∈ Ioo (G.left p) (G.right p) →
      |loss x * W sign x| ≤ lossCost p * ratio sign p * base sign p := by
    intro sign p x hx
    exact innerMorseInnerWeight_localized_piece_bound N K G
      ha hγ (hσ sign) hN hNa l r p hx
  have hlocalV : ∀ sign p x, x ∈ Ioo (G.left p) (G.right p) →
      |W (!sign) x| ≤ ratio sign p / base sign p := by
    intro sign p x hx
    rw [hopp sign x]
    exact (innerMorseInnerWeight_piece_bounds N K ha hγ (hσ sign) hN hNa G l r p hx).2
  apply C.inverse_localized_hardy_bound_of_piece_data W hW hpos
    (fun _ => CW) hCW hInv loss hloss hlossBound hw w hwpos hwInv hκ hsep hmodels
    hη hηsmall hKP hCE (mul_nonneg hKD (rpow_nonneg (exp_pos _).le _)) hj hjhalf
    (fun p M hp sign => by simpa only [ite_true, rpow_one] using herror p M hp sign)
    hcolumns hgapData hendpoints lossCost
    (fun p => (innerCoefficientLoss_pos N 37 _).le)
    ratio base (fun _ _ => sqrt_nonneg _) (fun sign p => innerMorseInnerPieceBase_pos _ _ _ _ _ _)
    hcenterW hcenterV hlocalW hlocalV
  intro sign p
  exact C.matched_piece_dirichlet_fixed37 hw hKD hcost p

end InnerRadialActualChain

end ContinuousFlexibility.Radial
