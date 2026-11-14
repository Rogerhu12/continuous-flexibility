module

public import ContinuousFlexibility.Radial.InnerRadialWeightedPoisson
public import ContinuousFlexibility.Radial.InnerInterfaceHilbertInverse

/-!
# Both weight signs for the same actual Poisson operator

The field weight is the genuine multiplier on the supported physical
source. Its boundary counterpart is the diagonal equivalence on the
same cut space. Their inverse signs are identified by the public
equivalence formulas and the inverse of a positive diagonal matrix.

The final bound uses the actual local model columns and one set of
gap slope and constant-weight data. The reciprocal gap data are
derived here. No global Poisson bound, interface smallness, or
commutation assumption is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

/-- The two reciprocal signs of one scalar weight function. -/
def innerSignedWeight {α : Type*} (W : α → ℝ) (sign : Bool) : α → ℝ :=
  fun x => if sign then W x else (W x)⁻¹

/-- Whole-function forms also identify partially applied multipliers. -/
theorem innerSignedWeight_true {α : Type*} (W : α → ℝ) :
    innerSignedWeight W true = W := rfl

theorem innerSignedWeight_false {α : Type*} (W : α → ℝ) :
    innerSignedWeight W false = (fun x => (W x)⁻¹) := rfl

theorem innerSignedWeight_measurable {α : Type*} [MeasurableSpace α]
    (W : α → ℝ) (hW : Measurable W) (sign : Bool) :
    Measurable (innerSignedWeight W sign) := by
  cases sign with
  | false => exact hW.inv
  | true => exact hW

theorem innerSignedWeight_pos {α : Type*} (W : α → ℝ)
    (hW : ∀ x, 0 < W x) (sign : Bool) (x : α) :
    0 < innerSignedWeight W sign x := by
  cases sign with
  | false => exact inv_pos.mpr (hW x)
  | true => exact hW x

theorem innerSignedWeight_abs_le {α : Type*} (W : α → ℝ)
    (C Cinv : ℝ) (hWC : ∀ x, |W x| ≤ C)
    (hWinv : ∀ x, |(W x)⁻¹| ≤ Cinv) (sign : Bool) (x : α) :
    |innerSignedWeight W sign x| ≤ if sign then C else Cinv := by
  cases sign with
  | false => exact hWinv x
  | true => exact hWC x

theorem innerSignedWeight_eqOn {α : Type*} (W : α → ℝ) (c : ℝ) (s : Set α)
    (hconstant : EqOn W (fun _ => c) s) (sign : Bool) :
    EqOn (innerSignedWeight W sign) (fun _ => if sign then c else c⁻¹) s := by
  intro x hx
  simp only [innerSignedWeight, hconstant hx]

/-- Restriction preserves the reciprocal sign; the unused exterior
entry remains one for either sign. -/
theorem innerChainScalarRestriction_signedWeight (n : ℕ) (p : Fin (n + 1))
    (w : Fin n → ℝ) (sign : Bool) (i : Fin 2) :
    innerChainScalarRestriction n p (innerSignedWeight w sign) 1 i =
      if sign then innerChainScalarRestriction n p w 1 i
      else (innerChainScalarRestriction n p w 1 i)⁻¹ := by
  change innerChainScalarRestriction n p
      (fun k => if sign then w k else (w k)⁻¹) 1 i =
    if sign then innerChainScalarRestriction n p w 1 i
    else (innerChainScalarRestriction n p w 1 i)⁻¹
  simpa only [inv_one, ite_self] using
    innerChainScalarRestriction_map n p w 1 (fun x => if sign then x else x⁻¹) i

section SupportedWeight

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (s : Set α) (hs : MeasurableSet s) (bordered : Bool)
  (W : α → ℝ) (hW : Measurable W) (hpos : ∀ x, 0 < W x)
  (C Cinv : ℝ) (hWC : ∀ x, |W x| ≤ C) (hWinv : ∀ x, |(W x)⁻¹| ≤ Cinv)

/-- Both equivalence signs are the actual supported multipliers. -/
theorem innerSupportedWeightEquiv_signed_toCLM (sign : Bool) :
    (innerHilbertWeight
        (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv) sign :
      ↥(innerSupportedAdmissibleSource μ s bordered) →L[ℝ]
        ↥(innerSupportedAdmissibleSource μ s bordered)) =
      innerSupportedWeightMultiplier μ s hs bordered (innerSignedWeight W sign)
        (innerSignedWeight_measurable W hW sign) (if sign then C else Cinv)
        (innerSignedWeight_abs_le W C Cinv hWC hWinv sign) := by
  cases sign with
  | false =>
    simpa only [innerHilbertWeight, innerSignedWeight_false, Bool.false_eq_true, ite_false] using
      innerSupportedWeightEquiv_symm_toCLM μ s hs bordered W hW hpos C Cinv hWC hWinv
  | true =>
    simpa only [innerHilbertWeight, innerSignedWeight_true, ite_true] using
      innerSupportedWeightEquiv_toCLM μ s hs bordered W hW hpos C Cinv hWC hWinv

end SupportedWeight

/-- The opposite boundary-equivalence sign is the inverse diagonal of
the same signed cut weight. -/
theorem innerMatrixEquiv_signed_inverse_toCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (sign : Bool) :
    (innerHilbertWeight
        (innerMatrixEquiv (Matrix.diagonal w)
          (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr hw))) (!sign) :
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      innerBoundaryDiagonal (fun i => (innerSignedWeight w sign i)⁻¹) := by
  cases sign with
  | false =>
    simp only [Bool.not_false, innerHilbertWeight, innerMatrixEquiv_toCLM,
      innerSignedWeight, Bool.false_eq_true, ite_false, inv_inv, innerBoundaryDiagonal]
  | true =>
    simp only [Bool.not_true, innerHilbertWeight, innerMatrixEquiv_symm_toCLM,
      innerBoundaryWeightMatrix_inv w (fun i => (hw i).ne'),
      innerSignedWeight, ite_true, innerBoundaryDiagonal]

section PoissonIdentity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (s : Set α) (hs : MeasurableSet s) (bordered : Bool)
  (W : α → ℝ) (hW : Measurable W) (hpos : ∀ x, 0 < W x)
  (C Cinv : ℝ) (hWC : ∀ x, |W x| ≤ C) (hWinv : ∀ x, |(W x)⁻¹| ≤ Cinv)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : ι → ℝ) (hw : ∀ i, 0 < w i)
  (T : EuclideanSpace ℝ ι →L[ℝ] ↥(innerSupportedAdmissibleSource μ s bordered))
  (J : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)

/-- Exact identification with the physical multiplier composition
estimated by the actual finite-chain Poisson theorem. -/
theorem innerWeightedPoisson_supported_eq (sign : Bool) :
    innerWeightedPoisson
      (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv)
      (innerMatrixEquiv (Matrix.diagonal w)
        (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr hw))) T J sign =
      (innerSupportedWeightMultiplier μ s hs bordered (innerSignedWeight W sign)
          (innerSignedWeight_measurable W hW sign) (if sign then C else Cinv)
          (innerSignedWeight_abs_le W C Cinv hWC hWinv sign) ∘L
        T ∘L innerBoundaryDiagonal (fun i => (innerSignedWeight w sign i)⁻¹)) ∘L J := by
  rw [innerWeightedPoisson,
    innerSupportedWeightEquiv_signed_toCLM μ s hs bordered W hW hpos C Cinv hWC hWinv sign,
    innerMatrixEquiv_signed_inverse_toCLM w hw sign]
  simp only [ContinuousLinearMap.comp_assoc]

end PoissonIdentity

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- Actual local columns and the original gap data give both signs
on one supported Poisson operator and one full reference matrix. -/
theorem weighted_poisson_both_signs (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (hpos : ∀ r, 0 < W r)
    (CW Cinv : ℝ) (hWC : ∀ r, |W r| ≤ CW) (hWinv : ∀ r, |(W r)⁻¹| ≤ Cinv)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hj : 0 < j)
    (hκ : ∀ i, 0 < C.kappa i)
    (hmodelκ : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → ∀ i, 0 < M.kappa i)
    (hmodels : ∀ sign : Bool, ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → ∀ i,
        ‖(innerChainScalarRestriction n p (innerSignedWeight w sign) 1 i *
            Real.sqrt (M.kappa i))⁻¹ •
          innerBorderFieldMap (radialHilbertMeasure D)
            (innerWeightMultiplier (radialHilbertMeasure D) (innerSignedWeight W sign)
              (innerSignedWeight_measurable W hW sign) (if sign then CW else Cinv)
              (innerSignedWeight_abs_le W CW Cinv hWC hWinv sign)) (M.column i)‖ ≤ K / j)
    (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p), C.piece p = Sum.inr Q →
      s ≤ Q.slope ∧ ∃ c : ℝ, 0 < c ∧
        EqOn W (fun _ => c) (Ioo (G.left p) (G.right p)) ∧
        (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p w 1 1 = c))
    (sign : Bool) :
    ‖innerWeightedPoisson
      (innerSupportedWeightEquiv (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
        bordered W hW hpos CW Cinv hWC hWinv)
      (innerMatrixEquiv (Matrix.diagonal w)
        (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr hw)))
      (C.poisson hDw)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (innerInterfaceInverseSqrt C.referenceMatrix)) sign‖ ≤
      max (2 * K) (Real.sqrt (12 / s)) / j := by
  have hgapSign : ∀ p (Q : InnerRadialGapChart D G j central p),
      C.piece p = Sum.inr Q →
      s ≤ Q.slope ∧ ∃ c : ℝ, 0 < c ∧
        EqOn (innerSignedWeight W sign) (fun _ => c) (Ioo (G.left p) (G.right p)) ∧
        (0 < p.val → innerChainScalarRestriction n p (innerSignedWeight w sign) 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p (innerSignedWeight w sign) 1 1 = c) := by
    intro p Q hp
    obtain ⟨hslope, c, hc, hconstant, hleft, hright⟩ := hgaps p Q hp
    refine ⟨hslope, (if sign then c else c⁻¹), ?_, ?_, ?_, ?_⟩
    · cases sign with
      | false => exact inv_pos.mpr hc
      | true => exact hc
    · exact innerSignedWeight_eqOn W c _ hconstant sign
    · intro hp
      rw [innerChainScalarRestriction_signedWeight, hleft hp]
    · intro hp
      rw [innerChainScalarRestriction_signedWeight, hright hp]
  rw [innerWeightedPoisson_supported_eq (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
    bordered W hW hpos CW Cinv hWC hWinv w hw (C.poisson hDw)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (innerInterfaceInverseSqrt C.referenceMatrix)) sign]
  exact (C.weighted_poisson_norm_le_ambient hDw (innerSignedWeight W sign)
    (innerSignedWeight_measurable W hW sign) (if sign then CW else Cinv)
    (innerSignedWeight_abs_le W CW Cinv hWC hWinv sign)
    (innerSignedWeight w sign)).trans
      (C.weighted_poisson_bound hDw (innerSignedWeight W sign)
        (innerSignedWeight_measurable W hW sign) (if sign then CW else Cinv)
        (innerSignedWeight_abs_le W CW Cinv hWC hWinv sign)
        (innerSignedWeight w sign) (innerSignedWeight_pos w hw sign)
        hK hs hj hκ hmodelκ (hmodels sign) hgapSign)

end InnerRadialActualChain

end ContinuousFlexibility.Radial
