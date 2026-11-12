import ContinuousFlexibility.Radial.MatchedInnerActualWeights
import ContinuousFlexibility.Radial.MatchedInnerUnitWeights
import ContinuousFlexibility.Radial.InnerRadialDirichletWeights
import ContinuousFlexibility.Radial.InnerRadialWeightedPoisson
import ContinuousFlexibility.Radial.InnerRadialInterfaceWeights

/-!
# Local physical estimates for the same weighted inner inverse

The inputs are the original unweighted piece costs, actual model-column
bounds and local two-cut errors, together with the true gap slope and
weight constancy. All global weighted Dirichlet, Poisson and interface
bounds are derived for one actual chain C. The constants remain explicit
and may be fixed before the chain geometry is chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

section SupportedSigns

variable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (bordered : Bool)
    (W : Bool → α → ℝ) (hW : ∀ sign, Measurable (W sign))
    (hpos : ∀ sign x, 0 < W sign x)
    (B : Bool → ℝ) (hB : ∀ sign x, |W sign x| ≤ B sign)
    (hInv : ∀ x, W false x = (W true x)⁻¹)

local notation "E" => innerSupportedWeightEquiv μ s hs bordered
  (W true) (hW true) (hpos true) (B true) (B false) (hB true)
  (fun x => Eq.trans_le (congrArg abs (Eq.symm (hInv x))) (hB false x))

/-- Its continuous equivalence is the same identity, so the first band
uses the unweighted inverse without any new operator representation. -/
theorem innerSupportedWeightEquiv_one :
    innerSupportedWeightEquiv μ s hs bordered (fun _ => (1 : ℝ))
      measurable_const (fun _ => zero_lt_one) 1 1
      (fun _ => by norm_num) (fun _ => by norm_num) =
        ContinuousLinearEquiv.refl ℝ (↥(innerSupportedAdmissibleSource μ s bordered)) := by
  have hh := (innerSupportedWeightEquiv_toCLM μ s hs bordered (fun _ => (1 : ℝ))
    measurable_const (fun _ => zero_lt_one) 1 1
    (fun _ => by norm_num) (fun _ => by norm_num)).trans
      (innerSupportedWeightMultiplier_one μ s hs bordered)
  apply ContinuousLinearEquiv.ext
  funext F
  exact congrArg (fun T : (↥(innerSupportedAdmissibleSource μ s bordered)) →L[ℝ] (↥(innerSupportedAdmissibleSource μ s bordered)) => T F) hh

/-- Both given physical weight functions are the two signs of the
one original supported continuous equivalence. -/
theorem innerSupportedWeightEquiv_pair_sign (sign : Bool) :
    (innerHilbertWeight E sign : (↥(innerSupportedAdmissibleSource μ s bordered)) →L[ℝ] (↥(innerSupportedAdmissibleSource μ s bordered))) =
      innerSupportedWeightMultiplier μ s hs bordered
        (W sign) (hW sign) (B sign) (hB sign) := by
  have hfun : (fun x => (W true x)⁻¹) = W false :=
    funext (fun x => (hInv x).symm)
  cases sign
  · simpa only [innerHilbertWeight, hfun] using
      innerSupportedWeightEquiv_symm_toCLM μ s hs bordered
        (W true) (hW true) (hpos true) (B true) (B false) (hB true)
        (fun x => Eq.trans_le (congrArg abs (Eq.symm (hInv x))) (hB false x))
  · exact innerSupportedWeightEquiv_toCLM μ s hs bordered
      (W true) (hW true) (hpos true) (B true) (B false) (hB true)
      (fun x => Eq.trans_le (congrArg abs (Eq.symm (hInv x))) (hB false x))

end SupportedSigns

/-- The inverse of the actual positive diagonal has its pointwise
reciprocal entries, including a zero-dimensional cut space. -/
theorem innerPositiveDiagonal_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (Matrix.diagonal w)⁻¹ = Matrix.diagonal (fun i => (w i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  ext i k
  rw [Matrix.mul_diagonal]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, inv_mul_cancel₀ (hw i).ne']
  · simp only [Matrix.diagonal_apply_ne _ hik, Matrix.one_apply_ne hik, zero_mul]

/-- The opposite cut sign in the same matrix equivalence is precisely
the diagonal used in the original local Poisson estimates. -/
theorem innerMatrixEquiv_pair_opposite_sign {n : ℕ}
    (w : Bool → Fin n → ℝ) (hw : ∀ i, 0 < w true i)
    (hInv : ∀ i, w false i = (w true i)⁻¹)
    (hΩ : IsUnit (Matrix.diagonal (w true))) (sign : Bool) :
    (innerHilbertWeight (innerMatrixEquiv (Matrix.diagonal (w true)) hΩ) (!sign) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
        innerBoundaryDiagonal (fun i => (w sign i)⁻¹) := by
  cases sign
  · rw [innerMatrixEquiv_weight_toCLM]
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (w true)) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (Matrix.diagonal (fun i => (w false i)⁻¹))
    congr 2
    funext i
    rw [hInv, inv_inv]
  · rw [innerMatrixEquiv_weight_toCLM]
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (w true))⁻¹ =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (Matrix.diagonal (fun i => (w true i)⁻¹))
    rw [innerPositiveDiagonal_inv (w true) hw]

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
    {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
    (C : InnerRadialActualChain D G bordered j central column)
    (W : Bool → ℝ → ℝ) (hW : ∀ sign, Measurable (W sign))
    (hpos : ∀ sign x, 0 < W sign x)
    (B : Bool → ℝ) (hB : ∀ sign x, |W sign x| ≤ B sign)
    (hInv : ∀ x, W false x = (W true x)⁻¹)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "E" => innerSupportedWeightEquiv (radialHilbertMeasure D)
  (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) bordered
  (W true) (hW true) (hpos true) (B true) (B false) (hB true)
  (fun x => Eq.trans_le (congrArg abs (Eq.symm (hInv x))) (hB false x))
local notation "sets" => (fun p : Fin (n + 1) => Ioo (G.left p) (G.right p))

/-- Actual local data imply both weighted estimates for the original
physical inverse. No bound on a globally weighted operator is an input. -/
theorem inverse_weighted_bound_of_piece_data
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
    (ratio base : Bool → Fin (n + 1) → ℝ)
    (hratio : ∀ sign p, 0 ≤ ratio sign p)
    (hbase : ∀ sign p, 0 < base sign p)
    (hcenterW : ∀ sign, 1 ≤ ratio sign central * base sign central)
    (hcenterV : ∀ sign, 1 ≤ ratio sign central / base sign central)
    (hlocalW : ∀ sign p x, x ∈ sets p →
      |W sign x| ≤ ratio sign p * base sign p)
    (hlocalV : ∀ sign p x, x ∈ sets p →
      |W (!sign) x| ≤ ratio sign p / base sign p)
    (hcost : ∀ sign p, ratio sign p ^ 2 * ‖(C.piece p).dirichlet hw‖ ≤ d) :
    ∃ hS : IsUnit C.fluxMatrix, ∀ sign : Bool,
      ‖(innerHilbertWeight E sign : H →L[ℝ] H) ∘L C.inverse hw hS ∘L
        (innerHilbertWeight E (!sign) : H →L[ℝ] H)‖ ≤
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
  intro sign
  have hD :
      ‖(innerHilbertWeight E sign : H →L[ℝ] H) ∘L C.dirichlet hw ∘L
        (innerHilbertWeight E (!sign) : H →L[ℝ] H)‖ ≤ d := by
    rw [hE sign, hE (!sign)]
    have hh := C.dirichlet_weighted_piece_cost hw (W sign) (W (!sign))
      (hW sign) (hW (!sign)) (B sign) (B (!sign)) (hB sign) (hB (!sign))
      (fun _ => 1) (ratio sign) (base sign) (fun _ => zero_le_one) (hratio sign) (hbase sign)
      (by simpa only [one_mul] using hcenterW sign) (hcenterV sign)
      (by simpa only [one_mul] using hlocalW sign) (hlocalV sign) hd
      (by simpa only [one_mul] using hcost sign)
    simpa only [innerRadialSupportedMultiplier] using hh
  exact C.inverse_weighted_bound hw hS hκ (w true) (hwpos true)
    hgapCuts hsep hmodels hη hηsmall herror
    E (innerSupportedWeightEquiv_selfAdjoint _ _ _ _ _ _ _ _ _ _ _)
    hCP hj hP sign hD

end InnerRadialActualChain

/-- Once the frequency is at least one, the same scalar bound can be
chosen before a chain geometry or retained length is instantiated. -/
theorem innerActualInverse_uniform_cost {d CP j : ℝ}
    (hj : 1 ≤ j) :
    d + 2 * CP ^ 2 / j ^ 2 ≤ d + 2 * CP ^ 2 := by
  exact add_le_add le_rfl (div_le_self (by positivity) (one_le_pow₀ hj))

end ContinuousFlexibility.Radial
