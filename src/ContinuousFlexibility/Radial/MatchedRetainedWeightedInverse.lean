import ContinuousFlexibility.Radial.RetainedMorseChainInverse
import ContinuousFlexibility.Radial.MatchedRetainedMorseColumns
import ContinuousFlexibility.Radial.MatchedInnerFiniteWeightedInverse

/-!
# Both signed bounds for the same retained Morse inverse

The original central model and every original selected Morse model form
one actual retained chain. Its actual columns, conormal errors, endpoint
energy and unweighted Dirichlet bounds supply the finite-chain theorem.
The constants depend on the fixed model suppliers, before the frequency
and the retained transition index are chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length T : ℝ}
  (P : SeedRetainedPair S K q length) {Γ : ConnectedReferenceGeometry}
  (hD : RadialProfileGeometry Γ.reference) (hw : Γ.reference.w = P.pair.profile)
  (hS : IsSelectedTail S) (G₀ : MorseChainGeometryWitness S.chain)
  (hfirst : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  (hq : 0 < q) (hT : 0 < T)
  (hleft : Γ.centralLeft = exp K.left) (hright : Γ.centralRight = exp K.right)
  (hTL : Γ.centralLeft < centralRadius (-T)) (hTR : centralRadius T < Γ.centralRight)
  (k : ℕ) (hk : 0 < k)
  (hbridge : ∀ side r, r ∈ uIcc (S.cut side S.chain.index)
    (S.entry side S.chain.index) → 0 < deriv (S.family S.sigma).w r)
  (hmodel : EqOn Γ.reference.w (centralRadialProfile 1) (Ioo Γ.centralLeft Γ.centralRight))
  (hwindow : ∀ r, 0 < r → (r ≤ centralRadius (-T) ∨ centralRadius T ≤ r) →
    (3 / 4 : ℝ) ≤ r * deriv (centralRadialProfile 1) r / centralRadialProfile 1 r)
  (bordered : Bool) (j : ℝ) (hj : 1 ≤ j) (column : RadialModeL2 Γ.reference)

local notation "H" => P.retainedMorseInnerGeometry hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk
local notation "center" => innerModelChainPiece (innerMorseInnerCenter k)

variable {CM KM : ℝ}
  (hB : ∀ side p, BufferHypotheses
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)))
  (models : ∀ side p, InnerBufferLocalizedData
    (innerMorseBufferData
      (morseChainA S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      (morseChainB S.chain (innerMorseInnerTailIndex S.chain.index k side p))
      j (8 * (S.chain.d (innerMorseInnerTailIndex S.chain.index k side p) : ℝ) ^ 9)) CM KM)
  (centralModel : InnerRadialModelChart Γ.reference H bordered j center column center)

local notation "tails" => P.retainedMorseInnerGeometry_tail hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk
local notation "MF" => P.retainedMorseModelFamily hw hS G₀ hfirst H bordered j column
  tails hB models centralModel
local notation "QF" => P.retainedMorseGapChart hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk hbridge hmodel hwindow j (zero_lt_one.trans_le hj)
local notation "A" => P.retainedMorseActualChain hD hw hS G₀ hfirst hq hT
  hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j
  (zero_lt_one.trans_le hj) column hB models centralModel
local notation "modelInduction" => P.retainedMorseActualChain_model_induction hD hw hS G₀
  hfirst hq hT hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j
  (zero_lt_one.trans_le hj) column hB models centralModel


local notation "σ" => fun sign : Bool => if sign then (1 : ℝ) else -1
local notation "W" => fun sign x => (innerMorseInnerWeight S.chain.index k 0 1 H
  (A).matchedWeightLeft (A).matchedWeightRight x) ^ (σ sign)
local notation "w" => fun sign i =>
  (innerMorseInnerInterfaceWeight S.chain.index k 0 1 i) ^ (σ sign)
local notation "hW" => fun sign => (innerMorseInnerWeight_measurable S.chain.index k 0 1 H
  (A).matchedWeightLeft (A).matchedWeightRight).pow_const (σ sign)
local notation "loss" => innerMorseInnerLoss S.chain.index k H 37
local notation "hloss" => innerMorseInnerLoss_measurable S.chain.index k H 37
local notation "hlossBound" =>
  innerMorseInnerLoss_le_one S.chain.index k H (by norm_num : (0 : ℝ) ≤ 37)

include hbridge hmodel hwindow hB hj in
theorem retainedMorseActualChain_signed_inverse_bound
    {Dc Bc Lc : ℝ}
    (hCM : 0 < CM) (hDc : 0 ≤ Dc) (hBc : 0 ≤ Bc) (hLc : 0 ≤ Lc)
    (hN : 4096 ≤ S.chain.index)
    (hcentral : ∀ i, 0 < centralModel.kappa i)
    (hdir₀ : ‖centralModel.dirichlet‖ ≤ Dc)
    (hcolumns₀ : ∀ i,
      ‖(sqrt (centralModel.kappa i))⁻¹ • centralModel.column i‖ ≤ Bc / j)
    (hendpoints₀ : ∀ i,
      Γ.reference.w (if i = 0 then (H).left center else (H).right center) /
        (if i = 0 then (H).left center else (H).right center) ≤ Lc * centralModel.kappa i)
    (herror₀ : ∀ sign : Bool,
      ‖innerTwoCutWeightedError centralModel.kappa (fun _ => 1)
        centralModel.errorMatrix sign‖ ≤ (1 : ℝ) / 8)
    (hrem : ∀ side p i, innerMorseModelNormalizedRemainder (models side p) i ≤ 1 / j)
    (herror : ∀ side p height, 0 < height → ∀ sign : Bool,
      ‖innerTwoCutWeightedError
        (innerPhysicalCutKappa height (fun _ => 1)
          (fun i => ((models side p).column i).inwardEnergy))
        (innerMorseCutWeight S.chain.index 0 1 side
          (innerMorseInnerTailIndex S.chain.index k side p))
        ((models side p).physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8) :
    ∃ CW : ℝ, ∃ hCW : ∀ sign x, |W sign x| ≤ CW,
    ∃ hmatrix : IsUnit (A).fluxMatrix, ∀ sign : Bool,
      ‖innerSupportedWeightMultiplier (radialHilbertMeasure Γ.reference)
          (innerRadialChainRegion Γ.reference H) (innerRadialChainRegion_measurable Γ.reference H)
          bordered (fun x => loss x * W sign x) ((hloss).mul (hW sign)) CW
          (innerWeight_mul_bound_one loss (W sign) hlossBound CW (hCW sign)) ∘L
        (A).inverse hD.2.2.1.1 hmatrix ∘L
        innerSupportedWeightMultiplier (radialHilbertMeasure Γ.reference)
          (innerRadialChainRegion Γ.reference H) (innerRadialChainRegion_measurable Γ.reference H)
          bordered (W (!sign)) (hW (!sign)) CW (hCW (!sign))‖ ≤
        retainedMorseDirichletCoefficient Dc CM * radialE S.chain.index ^ (37 : ℝ) +
          2 * (max ((2 * retainedMorsePoissonCoefficient Bc / j) ^ 2) 48 +
            24 * retainedMorseEndpointCoefficient Lc CM) := by
  let d : ℝ := retainedMorseDirichletCoefficient Dc CM
  let p : ℝ := retainedMorsePoissonCoefficient Bc
  let l : ℝ := retainedMorseEndpointCoefficient Lc CM
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hDM : 0 ≤ innerMorseDirichletConstant CM := innerMorseDirichletConstant_nonneg hCM.le
  have hd : 0 ≤ d := by
    dsimp only [d, retainedMorseDirichletCoefficient]
    positivity
  have hp : 0 ≤ p := add_nonneg innerMorsePoissonConstant_pos.le hBc
  have hl : 0 ≤ l := add_nonneg (mul_nonneg (by norm_num) hCM.le) hLc
  have hcentralP : Bc / j ≤ p / j :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_left innerMorsePoissonConstant_pos.le) hjpos.le
  have htailP : innerMorsePoissonConstant / j ≤ p / j :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right hBc) hjpos.le
  have hσ : ∀ sign : Bool, |σ sign| ≤ 1 := by intro sign; cases sign <;> norm_num
  obtain ⟨CW, hCWone, hfinite⟩ := innerMorseInnerWeight_finite_bounds
    S.chain.index k 0 1 H (A).matchedWeightLeft (A).matchedWeightRight
  have hCW : ∀ sign x, |W sign x| ≤ CW := by
    intro sign x
    cases sign
    · simpa only [Bool.false_eq_true, ite_false, rpow_neg_one] using (hfinite x).2
    · simpa only [ite_true, rpow_one] using (hfinite x).1
  refine ⟨CW, hCW, ?_⟩
  have hκ : ∀ i, 0 < (A).kappa i :=
    P.retainedMorseActualChain_kappa_pos hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
      column hB models centralModel hCM hcentral
  have hmodelκ : ∀ p (M : InnerRadialModelChart Γ.reference H bordered j center column p),
      (A).piece p = .inl M → 0 < p.val ∧ p.val < 2 * (2 * k + 1) ∧ ∀ i, 0 < M.kappa i :=
    P.retainedMorseActualChain_model_internal hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
      column hB models centralModel hCM hcentral
  have hgapShape : ∀ r (Q : InnerRadialGapChart Γ.reference H j center r),
      (A).piece r = .inr Q → ∃ g : Fin (2 * k + 2), r = innerModelChainGap g := by
    intro r Q hQ
    rcases innerModelChainPiece_or_gap r with ⟨r, rfl⟩ | ⟨g, rfl⟩
    · rw [retainedMorseActualChain_model] at hQ
      cases hQ
    · exact ⟨g, rfl⟩
  have herr := modelInduction
    (fun r M => ∀ sign : Bool,
      ‖innerTwoCutWeightedError M.kappa
        (innerChainScalarRestriction (2 * (2 * k + 1)) r
          (innerMorseInnerInterfaceWeight S.chain.index k 0 1) 1)
        M.errorMatrix sign‖ ≤ (1 : ℝ) / 8)
    (fun sign => by
      simpa only [innerMorseInnerInterfaceWeight_model, innerMorseInnerModelWeight_center]
        using herror₀ sign)
    (fun side r sign => by
      have hh := P.retainedMorseModelChart_weighted_error_bound hw hS G₀ hfirst H
        bordered j center (innerModelChainPiece (innerMorseInnerTailSlot k side r)) column
        side (innerMorseInnerTailIndex S.chain.index k side r)
        (innerMorseInnerTailIndex_bounds _ _ _ _).1
        (innerMorseInnerTailPiece_ne_center _ _ _) (tails side r).1 (tails side r).2
        (hB side r) (models side r) S.chain.index 0 1 (1 / 8) (herror side r) sign
      simpa only [innerMorseInnerInterfaceWeight_model, innerMorseInnerModelWeight_tail] using hh)
  have hcols (sign : Bool) := modelInduction
    (fun r M => ∀ i,
      ‖(innerChainScalarRestriction (2 * (2 * k + 1)) r (w sign) 1 i *
          sqrt (M.kappa i))⁻¹ •
        innerBorderFieldMap (radialHilbertMeasure Γ.reference)
          (innerWeightMultiplier (radialHilbertMeasure Γ.reference)
            (W sign) (hW sign) CW (hCW sign)) (M.column i)‖ ≤ p / j)
    (fun i => by
      rw [matchedInner_central_weighted_column_norm S.chain.index k 0 1 (σ sign) H
        (A).matchedWeightLeft (A).matchedWeightRight centralModel CW (hCW sign) i]
      exact (hcolumns₀ i).trans hcentralP)
    (fun side r i => by
      have hpiece := P.retainedMorseActualChain_tail hD hw hS G₀ hfirst hq hT
        hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
        column hB models centralModel side r
      exact (P.retainedMorseModelChart_actual_weighted_column_bound
        hw hS G₀ hfirst k H bordered j column side r (tails side r).1 (tails side r).2
        (hB side r) (models side r) A hpiece
        (by norm_num) (by norm_num) (hσ sign) hN (by positivity) hj hCM (hrem side r)
        CW (hCW sign) i).trans htailP)
  have hends := modelInduction
    (fun p M => ∀ i, Γ.reference.w (if i = 0 then (H).left p else (H).right p) /
      (if i = 0 then (H).left p else (H).right p) ≤ l * M.kappa i)
    (fun i => (hendpoints₀ i).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left
        (mul_nonneg (by norm_num) hCM.le)) (hcentral i).le))
    (fun side p i =>
      (P.retainedMorseModelChart_endpoint_weight_bound hw hS G₀ hfirst H bordered j center
        (innerModelChainPiece (innerMorseInnerTailSlot k side p)) column
        side (innerMorseInnerTailIndex S.chain.index k side p)
        (innerMorseInnerTailIndex_bounds _ _ _ _).1
        (innerMorseInnerTailPiece_ne_center _ _ _) (tails side p).1 (tails side p).2
        (hB side p) (models side p) hj hCM i).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hLc)
        (P.retainedMorseTailModelChart_kappa_pos hw hS G₀ hfirst H bordered j column
          tails hB models hCM side p i).le))
  have hgapends : ∀ (i : Fin (2 * (2 * k + 1)))
      (Q : InnerRadialGapChart Γ.reference H j center i.succ),
      (A).piece i.succ = .inr Q →
        Γ.reference.w ((H).left i.succ) / (H).left i.succ ≤ l * (A).kappa i := by
    intro i Q hi
    obtain ⟨p, hs | hs⟩ := innerModelChain_cut_incidence i
    · rw [hs.2, retainedMorseActualChain_model] at hi
      cases hi
    · have hm := P.retainedMorseActualChain_model hD hw hS G₀ hfirst hq hT
        hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
        column hB models centralModel p
      have hed := hends (innerModelChainPiece p) (MF p) hm 1
      have hx : (H).left i.succ = (H).right (innerModelChainPiece p) := by
        rw [← hs.1]
        rfl
      rw [hx, (A).kappa_apply, hs.1, hm, hi]
      simpa only [InnerRadialActualPiece.kappa, Pi.zero_apply, add_zero,
        show (1 : Fin 2) ≠ 0 by decide, ite_false] using hed

  have hE (m : ℕ) : 1 ≤ radialE m ^ (36 : ℝ) := by
    rw [rpow_ofNat]
    exact one_le_pow₀ (one_le_exp.mpr (radialQ_nonneg m))
  have hDcentral : Dc ≤ d := by
    dsimp only [d, retainedMorseDirichletCoefficient]
    linarith only [hDM]
  have hDMbound : innerMorseDirichletConstant CM ≤ d := by
    dsimp only [d, retainedMorseDirichletCoefficient]
    linarith only [hDc]
  have h48 : (48 : ℝ) ≤ d := by
    dsimp only [d, retainedMorseDirichletCoefficient]
    linarith only [hDc, hDM]
  have hmodelD := modelInduction
    (fun r M => ‖M.dirichlet‖ ≤ d *
      radialE (innerMorseInnerPieceIndex S.chain.index k r) ^ (36 : ℝ))
    (by
      apply hdir₀.trans
      exact hDcentral.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hE _) hd))
    (fun side r => by
      rw [innerMorseInnerPieceIndex_model, innerMorseInnerModelIndex_tail]
      exact (P.retainedMorseModelChart_dirichlet_cost hw hS G₀ hfirst H bordered j center
        (innerModelChainPiece (innerMorseInnerTailSlot k side r)) column
        side (innerMorseInnerTailIndex S.chain.index k side r)
        (innerMorseInnerTailIndex_bounds _ _ _ _).1
        (innerMorseInnerTailPiece_ne_center _ _ _) (tails side r).1 (tails side r).2
        (hB side r) (models side r) hj hCM.le).trans
          (mul_le_mul_of_nonneg_right hDMbound (zero_le_one.trans (hE _))))
  have hdir : ∀ r, ‖((A).piece r).dirichlet hD.2.2.1.1‖ ≤
      d * radialE (innerMorseInnerPieceIndex S.chain.index k r) ^ (36 : ℝ) := by
    intro r
    cases hr : (A).piece r with
    | inl M => simpa only [hr, InnerRadialActualPiece.dirichlet] using hmodelD r M hr
    | inr Q =>
      have hh := (Q.dirichlet_norm_le_hardy hD.2.2.1.1 (by nlinarith only [hj])).trans
        (h48.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hE _) hd))
      simpa only [hr, InnerRadialActualPiece.dirichlet] using hh
  exact (A).inverse_morse_weighted_fixed_loss S.chain.index k H
    (A).matchedWeightLeft (A).matchedWeightRight 0 1 CW hCW hD.2.2.1.1
    (by norm_num) (by norm_num) hN (by positivity) hκ
    (P.retainedMorseActualChain_kappa_separated hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
      column hB models centralModel)
    hmodelκ hgapShape (by norm_num) (by norm_num) hp hl hd hjpos
    (by nlinarith only [hj]) herr (fun sign r M hr => hcols sign r M hr) hgapends hdir

end SeedRetainedPair

end ContinuousFlexibility.Radial
