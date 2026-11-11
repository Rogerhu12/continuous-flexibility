import ContinuousFlexibility.Radial.RetainedMorseActualChain
import ContinuousFlexibility.Radial.RetainedMorseUnweightedBounds
import ContinuousFlexibility.Radial.InnerActualUnweightedHardyInverse

/-!
# The actual unweighted inverse of the retained finite Morse chain

Every local model and gap is the entry of one actual physical
dictionary. The normalized errors invert its complete Schur matrix.
The constants below depend only on the fixed central and Morse model
bounds. In particular the construction of a long first cone does not
enter the final estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

def retainedMorseDirichletCoefficient (Dc CM : ℝ) : ℝ :=
  48 + Dc + innerMorseDirichletConstant CM

def retainedMorsePoissonCoefficient (Bc : ℝ) : ℝ :=
  innerMorsePoissonConstant + Bc

def retainedMorseEndpointCoefficient (Lc CM : ℝ) : ℝ := 30000 * CM + Lc

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

include hbridge hmodel hwindow hB hj in
theorem exists_retainedMorseChainInverse {Dc Bc Lc : ℝ}
    (hCM : 0 < CM) (hDc : 0 ≤ Dc) (hBc : 0 ≤ Bc) (hLc : 0 ≤ Lc)
    (hcentral : ∀ i, 0 < centralModel.kappa i)
    (hdir₀ : ‖centralModel.dirichlet‖ ≤ Dc)
    (hcolumns₀ : ∀ i, ‖(sqrt (centralModel.kappa i))⁻¹ • centralModel.column i‖ ≤
      Bc * (1 + j) ^ 2)
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
        (innerMorseCutWeight S.chain.index 0 0 side
          (innerMorseInnerTailIndex S.chain.index k side p))
        ((models side p).physicalFluxError height (fun _ => 1)) sign‖ ≤ (1 : ℝ) / 8) :
    ∃ inverse : InnerRadialPhysicalSource Γ.reference H bordered →L[ℝ]
        InnerRadialPhysicalSource Γ.reference H bordered,
      (∀ u F, InnerRadialPhysicalWeakGraph Γ.reference hD.2.2.1.1.continuous H
        bordered j center column u F ↔ inverse F = u) ∧
      ‖inverse‖ ≤ retainedMorseDirichletCoefficient Dc CM *
        radialE (S.chain.index + k) ^ (37 : ℝ) +
        8 * (retainedMorsePoissonCoefficient Bc) ^ 2 * (1 + j) ^ 4 +
        96 + 48 * retainedMorseEndpointCoefficient Lc CM ∧ IsSelfAdjoint inverse := by
  let e : ℝ := radialE (S.chain.index + k) ^ (37 : ℝ)
  let d : ℝ := retainedMorseDirichletCoefficient Dc CM * e
  let p : ℝ := retainedMorsePoissonCoefficient Bc
  let c : ℝ := j * p * (1 + j) ^ 2
  let l : ℝ := retainedMorseEndpointCoefficient Lc CM
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hDM : 0 ≤ innerMorseDirichletConstant CM := innerMorseDirichletConstant_nonneg hCM.le
  have he : 1 ≤ e := by
    dsimp only [e]
    rw [rpow_ofNat]
    exact one_le_pow₀ (one_le_exp.mpr (radialQ_nonneg _))
  have hcoeff : 0 ≤ retainedMorseDirichletCoefficient Dc CM := by
    unfold retainedMorseDirichletCoefficient
    positivity
  have hd : 0 ≤ d := mul_nonneg hcoeff (zero_le_one.trans he)
  have hp : 0 ≤ p := add_nonneg innerMorsePoissonConstant_pos.le hBc
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hjpos.le hp) (sq_nonneg _)
  have hl : 0 ≤ l := add_nonneg (mul_nonneg (by norm_num) hCM.le) hLc
  have hpoly : 1 ≤ (1 + j) ^ 2 := by nlinarith only [hj, sq_nonneg j]
  have hcdiv : c / j = p * (1 + j) ^ 2 := by
    dsimp only [c]
    field_simp [hjpos.ne'] <;> ring
  have hcentralP : Bc * (1 + j) ^ 2 ≤ c / j := by
    rw [hcdiv]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact le_add_of_nonneg_left innerMorsePoissonConstant_pos.le
  have htailP : innerMorsePoissonConstant / j ≤ c / j := by
    apply div_le_div_of_nonneg_right _ hjpos.le
    calc
      _ ≤ p := le_add_of_nonneg_right hBc
      _ ≤ j * p := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hp
      _ ≤ c := by simpa only [mul_one, c] using
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg hjpos.le hp)
  have hκ : ∀ i, 0 < (A).kappa i :=
    P.retainedMorseActualChain_kappa_pos hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
      column hB models centralModel hCM hcentral
  have hmodelκ : ∀ p (M : InnerRadialModelChart Γ.reference H bordered j center column p),
      (A).piece p = .inl M → 0 < p.val ∧ p.val < 2 * (2 * k + 1) ∧ ∀ i, 0 < M.kappa i :=
    P.retainedMorseActualChain_model_internal hD hw hS G₀ hfirst hq hT
      hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
      column hB models centralModel hCM hcentral
  have herr := modelInduction
    (fun _ M => ∀ sign : Bool,
      ‖innerTwoCutWeightedError M.kappa (fun _ => 1) M.errorMatrix sign‖ ≤ (1 : ℝ) / 8)
    herror₀ (fun side p sign =>
      P.retainedMorseModelChart_unweighted_error_bound hw hS G₀ hfirst H bordered j center
        (innerModelChainPiece (innerMorseInnerTailSlot k side p)) column
        side (innerMorseInnerTailIndex S.chain.index k side p)
        (innerMorseInnerTailIndex_bounds _ _ _ _).1
        (innerMorseInnerTailPiece_ne_center _ _ _) (tails side p).1 (tails side p).2
        (hB side p) (models side p) (herror side p) sign)
  have hcols := modelInduction
    (fun _ M => ∀ i, ‖(sqrt (M.kappa i))⁻¹ • M.column i‖ ≤ c / j)
    (fun i => (hcolumns₀ i).trans hcentralP)
    (fun side p i =>
      (P.retainedMorseModelChart_column_bound hw hS G₀ hfirst H bordered j center
        (innerModelChainPiece (innerMorseInnerTailSlot k side p)) column
        side (innerMorseInnerTailIndex S.chain.index k side p)
        (innerMorseInnerTailIndex_bounds _ _ _ _).1
        (innerMorseInnerTailPiece_ne_center _ _ _) (tails side p).1 (tails side p).2
        (hB side p) (models side p) hj hCM (hrem side p) i).trans htailP)
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
  have hDcBound : Dc ≤ d := by
    calc
      _ ≤ Dc * e := by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hDc
      _ ≤ d := mul_le_mul_of_nonneg_right
        (by dsimp only [retainedMorseDirichletCoefficient]; linarith only [hDM]) (zero_le_one.trans he)
  have h48 : (48 : ℝ) ≤ d := by
    calc
      _ ≤ 48 * e := by linarith only [he]
      _ ≤ d := mul_le_mul_of_nonneg_right
        (by dsimp only [retainedMorseDirichletCoefficient]; linarith only [hDc, hDM])
        (zero_le_one.trans he)
  have hmodelD := modelInduction (fun _ M => ‖M.dirichlet‖ ≤ d)
    (hdir₀.trans hDcBound) (fun side p =>
      (P.retainedMorseModelChart_dirichlet_cost_at_upper hw hS G₀ hfirst H bordered j center
        (innerModelChainPiece (innerMorseInnerTailSlot k side p)) column
        side (innerMorseInnerTailIndex S.chain.index k side p)
        (innerMorseInnerTailIndex_bounds _ _ _ _).1
        (innerMorseInnerTailPiece_ne_center _ _ _) (tails side p).1 (tails side p).2
        (hB side p) (models side p) hj hCM.le
        (innerMorseInnerTailIndex_bounds _ _ _ _).2.le).trans
      (mul_le_mul_of_nonneg_right
        (by dsimp only [retainedMorseDirichletCoefficient]; linarith only [hDc])
        (zero_le_one.trans he)))
  have hdir : ∀ p, ‖((A).piece p).dirichlet hD.2.2.1.1‖ ≤ d := by
    intro p
    cases hp : (A).piece p with
    | inl M => simpa only [hp, InnerRadialActualPiece.dirichlet] using hmodelD p M hp
    | inr Q =>
      simpa only [hp, InnerRadialActualPiece.dirichlet] using
        (Q.dirichlet_norm_le_hardy hD.2.2.1.1 (by nlinarith only [hj])).trans h48
  obtain ⟨inverse, hgraph, hnorm, hself⟩ :=
    (A).exists_unweighted_inverse_of_local_bounds_hardy hD.2.2.1.1 hc hl hd hjpos
      (by nlinarith only [hj]) hκ
      (P.retainedMorseActualChain_kappa_separated hD hw hS G₀ hfirst hq hT
        hleft hright hTL hTR k hk hbridge hmodel hwindow bordered j hjpos
        column hB models centralModel)
      hmodelκ (by norm_num) (by norm_num) herr hcols hgapends hdir
  refine ⟨inverse, hgraph, hnorm.trans ?_, hself⟩
  have hmax : max ((2 * c / j) ^ 2) 48 ≤ (2 * c / j) ^ 2 + 48 :=
    max_le (le_add_of_nonneg_right (by norm_num))
      (le_add_of_nonneg_left (sq_nonneg _))
  have hcquad : (2 * c / j) ^ 2 = 4 * p ^ 2 * (1 + j) ^ 4 := by
    dsimp only [c]
    field_simp [hjpos.ne'] <;> ring
  calc
    _ ≤ d + 2 * (((2 * c / j) ^ 2 + 48) + 24 * l) :=
      add_le_add (le_refl d) (mul_le_mul_of_nonneg_left
        (add_le_add hmax (le_refl (24 * l))) (by norm_num))
    _ = _ := by rw [hcquad]; dsimp only [d, e, p, l]; ring

end SeedRetainedPair

end ContinuousFlexibility.Radial
