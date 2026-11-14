module

public import ContinuousFlexibility.Radial.InnerRadialInterfaceWeights
public import ContinuousFlexibility.Radial.InnerRadialWeightedPoisson

/-!
# Weighted bounds for the same actual finite-chain inverse

The local model errors and gap cut weights supply the actual interface
factorization. The normalized Poisson maps are the physical maps whose
adjoints occur in the weak inverse, rather than separate norm witnesses.
An output coefficient-loss contraction preserves the frequency-decaying
correction. Thus the same inverse serves both coarse and localized bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "B" => EuclideanSpace ℝ (Fin n)

theorem inverse_eq_glued (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) :
    C.inverse hw hS = innerGluedInverse (C.dirichlet hw) (C.poisson hw)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹) := by
  apply ContinuousLinearMap.ext
  intro F
  rw [C.inverse_apply, innerGluedInverse_apply]

section WeightedBounds

variable (hw : ContDiff ℝ ∞ D.w)
  (hκ : ∀ i, 0 < C.kappa i) (w : Fin n → ℝ) (hwpos : ∀ i, 0 < w i)
  (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p), C.piece p = .inr Q →
    ∃ c : ℝ,
      (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
      (p.val < n → innerChainScalarRestriction n p w 1 1 = c))
  (hsep : ∀ i : Fin n,
    (C.piece i.castSucc).kappa 1 = 0 ∨ (C.piece i.succ).kappa 0 = 0)
  (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
    C.piece p = .inl M → 0 < p.val ∧ p.val < n ∧ ∀ i, 0 < M.kappa i)
  {η : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
  (herror : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
    C.piece p = .inl M → ∀ sign : Bool,
      ‖innerTwoCutWeightedError M.kappa (innerChainScalarRestriction n p w 1)
        M.errorMatrix sign‖ ≤ η)

local notation "Ω" =>
  innerMatrixEquiv (Matrix.diagonal w) (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr hwpos))
local notation "J" =>
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (innerInterfaceInverseSqrt C.referenceMatrix)

include hκ hgaps hsep hmodels hη hηsmall herror

/-- The correction is the same actual Poisson-adjoint correction used
by the physical weak inverse. No global smallness premise remains. -/
theorem correction_weighted_bound (W : H ≃L[ℝ] H)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H)) {K : ℝ} (hK : 0 ≤ K) (hj : 0 < j)
    (hP : ∀ sign : Bool,
      ‖innerWeightedPoisson W Ω (C.poisson hw) J sign‖ ≤ K / j) (sign : Bool) :
    ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
        innerCouplingCorrection (C.poisson hw)
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹) ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤ 2 * K ^ 2 / j ^ 2 :=
  innerCoupling_bound_from_interface C.referenceMatrix (Matrix.diagonal w) C.errorMatrix
    (C.referenceMatrix_posDef hw hκ) (Matrix.posDef_diagonal_iff.mpr hwpos)
    (C.referenceMatrix_commute w hgaps)
    (C.normalized_error_both hw hκ w hwpos hsep hmodels hη hηsmall herror)
    W (C.poisson hw) hW hK hj hP sign

/-- A coefficient-loss contraction acts on the output of the same
inverse. Its cost is needed only for the actual Dirichlet part. -/
theorem inverse_localized_weighted_bound (hS : IsUnit C.fluxMatrix)
    (W : H ≃L[ℝ] H) (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    (L : H →L[ℝ] H) (hL : ‖L‖ ≤ 1) {K d : ℝ} (hK : 0 ≤ K) (hj : 0 < j)
    (hP : ∀ sign : Bool,
      ‖innerWeightedPoisson W Ω (C.poisson hw) J sign‖ ≤ K / j) (sign : Bool)
    (hD : ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L C.dirichlet hw ∘L
      (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ d) :
    ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L C.inverse hw hS ∘L
      (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ d + 2 * K ^ 2 / j ^ 2 := by
  have hcorrection := C.correction_weighted_bound hw hκ w hwpos hgaps hsep hmodels
    hη hηsmall herror W hW hK hj hP sign
  have hcorrectionLoss :
      ‖L ∘L ((innerHilbertWeight W sign : H →L[ℝ] H) ∘L
          innerCouplingCorrection (C.poisson hw)
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹) ∘L
          (innerHilbertWeight W (!sign) : H →L[ℝ] H))‖ ≤ 2 * K ^ 2 / j ^ 2 := by
    calc
      _ ≤ ‖L‖ * ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
          innerCouplingCorrection (C.poisson hw)
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹) ∘L
          (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (2 * K ^ 2 / j ^ 2) :=
        mul_le_mul hL hcorrection (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [C.inverse_eq_glued hw hS]
  simp only [innerGluedInverse, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  exact (norm_add_le _ _).trans (add_le_add hD hcorrectionLoss)

end WeightedBounds

end InnerRadialActualChain

end ContinuousFlexibility.Radial
