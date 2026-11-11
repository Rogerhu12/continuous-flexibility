import ContinuousFlexibility.Radial.MatchedInnerLocalWeightedInverse
import ContinuousFlexibility.Radial.InnerSupportedWeightProducts

/-!
# The same inner inverse with its actual output coefficient loss

The physical output loss is retained as a supported field multiplier;
its scalar coordinate remains one. The local piece costs give the
Dirichlet estimate after this loss. Its norm is at most one, so the
already normalized Poisson correction costs no more. No global weighted
operator estimate is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

theorem innerWeight_mul_bound_one {α : Type*}
    (loss W : α → ℝ) (hloss : ∀ x, |loss x| ≤ 1)
    (B : ℝ) (hB : ∀ x, |W x| ≤ B) (x : α) :
    |loss x * W x| ≤ B := by
  rw [abs_mul]
  exact ((mul_le_mul_of_nonneg_right (hloss x) (abs_nonneg _)).trans_eq
    (one_mul _)).trans (hB x)

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
    {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
    (C : InnerRadialActualChain D G bordered j central column)
    (W : Bool → ℝ → ℝ) (hW : ∀ sign, Measurable (W sign))
    (hpos : ∀ sign x, 0 < W sign x)
    (B : Bool → ℝ) (hB : ∀ sign x, |W sign x| ≤ B sign)
    (hInv : ∀ x, W false x = (W true x)⁻¹)
    (loss : ℝ → ℝ) (hloss : Measurable loss) (hlossBound : ∀ x, |loss x| ≤ 1)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "E" => innerSupportedWeightEquiv (radialHilbertMeasure D)
  (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
  (W true) (hW true) (hpos true) (B true) (B false) (hB true)
  (fun x => Eq.trans_le (congrArg abs (Eq.symm (hInv x))) (hB false x))
local notation "MW" => fun sign : Bool =>
  innerSupportedWeightMultiplier (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (W sign) (hW sign) (B sign) (hB sign)
local notation "L" => innerSupportedWeightMultiplier (radialHilbertMeasure D)
  (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
  loss hloss 1 hlossBound
local notation "U" => fun sign : Bool =>
  innerSupportedWeightMultiplier (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
    (fun x => loss x * W sign x) (hloss.mul (hW sign)) (B sign)
    (innerWeight_mul_bound_one loss (W sign) hlossBound (B sign) (hB sign))
local notation "sets" => (fun p : Fin (n + 1) => Ioo (G.left p) (G.right p))

include hpos hInv

/-- Primitive actual piece, model-column and gap estimates give the
same physical inverse after the actual fixed output loss. -/
theorem inverse_localized_bound_of_piece_data
    (hw : ContDiff ℝ ∞ D.w)
    (w : Bool → Fin n → ℝ) (hwpos : ∀ sign i, 0 < w sign i)
    (hwInv : ∀ i, w false i = (w true i)⁻¹)
    (hκ : ∀ i, 0 < C.kappa i)
    (hsep : ∀ i : Fin n,
      (C.piece i.castSucc).kappa 1 = 0 ∨ (C.piece i.succ).kappa 0 = 0)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → 0 < p.val ∧ p.val < n ∧ ∀ i, 0 < M.kappa i)
    {η KP slope d : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (hKP : 0 ≤ KP) (hslope : 0 < slope) (hd : 0 ≤ d) (hj : 0 < j)
    (herror : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa (innerChainScalarRestriction n p (w true) 1)
          M.errorMatrix sign‖ ≤ η)
    (hcolumns : ∀ sign p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → ∀ i,
        ‖(innerChainScalarRestriction n p (w sign) 1 i * sqrt (M.kappa i))⁻¹ •
          innerBorderFieldMap (radialHilbertMeasure D)
            (innerWeightMultiplier (radialHilbertMeasure D)
              (W sign) (hW sign) (B sign) (hB sign)) (M.column i)‖ ≤ KP / j)
    (hgaps : ∀ sign p (Q : InnerRadialGapChart D G j central p),
      C.piece p = Sum.inr Q →
        slope ≤ Q.slope ∧ ∃ c : ℝ, 0 < c ∧
          EqOn (W sign) (fun _ => c) (sets p) ∧
          (0 < p.val → innerChainScalarRestriction n p (w sign) 1 0 = c) ∧
          (p.val < n → innerChainScalarRestriction n p (w sign) 1 1 = c))
    (lossCost : Fin (n + 1) → ℝ) (hlossCost : ∀ p, 0 ≤ lossCost p)
    (ratio base : Bool → Fin (n + 1) → ℝ)
    (hratio : ∀ sign p, 0 ≤ ratio sign p)
    (hbase : ∀ sign p, 0 < base sign p)
    (hcenterW : ∀ sign,
      1 ≤ lossCost central * ratio sign central * base sign central)
    (hcenterV : ∀ sign, 1 ≤ ratio sign central / base sign central)
    (hlocalW : ∀ sign p x, x ∈ sets p →
      |loss x * W sign x| ≤ lossCost p * ratio sign p * base sign p)
    (hlocalV : ∀ sign p x, x ∈ sets p →
      |W (!sign) x| ≤ ratio sign p / base sign p)
    (hcost : ∀ sign p,
      lossCost p * (ratio sign p ^ 2 * ‖(C.piece p).dirichlet hw‖) ≤ d) :
    ∃ hS : IsUnit C.fluxMatrix, ∀ sign : Bool,
      ‖U sign ∘L C.inverse hw hS ∘L MW (!sign)‖ ≤
        d + 2 * (max (2 * KP) (sqrt (12 / slope))) ^ 2 / j ^ 2 := by
  have hgapCuts : ∀ p (Q : InnerRadialGapChart D G j central p),
      C.piece p = Sum.inr Q → ∃ c : ℝ,
        (0 < p.val → innerChainScalarRestriction n p (w true) 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p (w true) 1 1 = c) := by
    intro p Q hp
    obtain ⟨_, c, _, _, hleft, hright⟩ := hgaps true p Q hp
    exact ⟨c, hleft, hright⟩
  have hS := C.fluxMatrix_isUnit_of_local_errors hw hκ (w true) (hwpos true)
    hgapCuts hsep hmodels hη hηsmall herror
  refine ⟨hS, ?_⟩
  have hΩ : (Matrix.diagonal (w true)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (hwpos true)
  have hCP : 0 ≤ max (2 * KP) (sqrt (12 / slope)) :=
    (mul_nonneg (by norm_num) hKP).trans (le_max_left _ _)
  have hE (sign : Bool) :
      (innerHilbertWeight E sign : H →L[ℝ] H) =
        innerSupportedWeightMultiplier (radialHilbertMeasure D)
          (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
          (W sign) (hW sign) (B sign) (hB sign) :=
    innerSupportedWeightEquiv_pair_sign _ _ _ _ W hW hpos B hB hInv sign
  have hP (sign : Bool) :
      ‖innerWeightedPoisson E (innerMatrixEquiv (Matrix.diagonal (w true)) hΩ.isUnit)
        (C.poisson hw) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt C.referenceMatrix)) sign‖ ≤
        max (2 * KP) (sqrt (12 / slope)) / j := by
    rw [innerWeightedPoisson, hE sign,
      innerMatrixEquiv_pair_opposite_sign w (hwpos true) hwInv hΩ.isUnit sign]
    have hp := (C.weighted_poisson_norm_le_ambient hw (W sign) (hW sign)
      (B sign) (hB sign) (w sign)).trans
        (C.weighted_poisson_bound hw (W sign) (hW sign) (B sign) (hB sign)
          (w sign) (hwpos sign) hKP hslope hj hκ
          (fun p M hp => (hmodels p M hp).2.2) (hcolumns sign) (hgaps sign))
    simpa only [ContinuousLinearMap.comp_assoc] using hp
  have hL : ‖L‖ ≤ 1 :=
    norm_innerSupportedCoefficientLoss_le_one (radialHilbertMeasure D)
      (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
        bordered loss hloss hlossBound
  have hproduct (sign : Bool) : L ∘L (innerHilbertWeight E sign : H →L[ℝ] H) = U sign := by
    rw [hE sign]
    have hBpos : 0 ≤ B sign := (abs_nonneg (W sign 0)).trans (hB sign 0)
    simpa only [one_mul] using
      (innerSupportedWeightMultiplier_product _ _ _ _ loss (W sign)
        hloss (hW sign) 1 (B sign) zero_le_one hBpos hlossBound (hB sign)).symm
  have hfactor (T : H →L[ℝ] H) (sign : Bool) :
      L ∘L ((innerHilbertWeight E sign : H →L[ℝ] H) ∘L T ∘L
        (innerHilbertWeight E (!sign) : H →L[ℝ] H)) =
      U sign ∘L T ∘L MW (!sign) := by
    rw [← ContinuousLinearMap.comp_assoc, hproduct sign, hE (!sign)]
  intro sign
  have hD :
      ‖L ∘L ((innerHilbertWeight E sign : H →L[ℝ] H) ∘L C.dirichlet hw ∘L
        (innerHilbertWeight E (!sign) : H →L[ℝ] H))‖ ≤ d := by
    rw [hfactor]
    exact C.dirichlet_weighted_piece_cost hw
      (fun x => loss x * W sign x) (W (!sign))
      (hloss.mul (hW sign)) (hW (!sign)) (B sign) (B (!sign))
      (innerWeight_mul_bound_one loss (W sign) hlossBound (B sign) (hB sign)) (hB (!sign))
      lossCost (ratio sign) (base sign) hlossCost (hratio sign) (hbase sign)
      (hcenterW sign) (hcenterV sign) (hlocalW sign) (hlocalV sign) hd (hcost sign)
  have hh := C.inverse_localized_weighted_bound hw hκ (w true) (hwpos true)
    hgapCuts hsep hmodels hη hηsmall herror hS
    E (innerSupportedWeightEquiv_selfAdjoint _ _ _ _ _ _ _ _ _ _ _)
    L hL hCP hj hP sign hD
  rw [hfactor] at hh
  exact hh

end InnerRadialActualChain

end ContinuousFlexibility.Radial
