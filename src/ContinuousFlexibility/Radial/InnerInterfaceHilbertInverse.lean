module

public import ContinuousFlexibility.Radial.InnerChainErrorAssembly
public import ContinuousFlexibility.Radial.InnerLocalizedInverseBound

/-!
# The same finite interface inverse in the physical Hilbert formula

The canonical matrix inverse gives a continuous equivalence on the actual
Euclidean cut space. Both diagonal-weight signs use this one equivalence
and this one inverse. The matrix Neumann factorization is transferred
exactly to the Hilbert operators used by the physical Schur construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped Matrix.Norms.L2Operator InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem innerMatrix_inverse_left_apply (S : Matrix ι ι ℝ) (hS : IsUnit S)
    (x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S⁻¹
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S x) = x := by
  have h := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))
    (Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS))
  have hx := congrArg (fun A => A x) h
  simpa only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] using hx

theorem innerMatrix_inverse_right_apply (S : Matrix ι ι ℝ) (hS : IsUnit S)
    (x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S⁻¹ x) = x := by
  have h := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))
    (Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS))
  have hx := congrArg (fun A => A x) h
  simpa only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] using hx

def innerMatrixEquiv (S : Matrix ι ι ℝ) (hS : IsUnit S) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  ContinuousLinearEquiv.equivOfInverse
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S)
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S⁻¹)
    (innerMatrix_inverse_left_apply S hS) (innerMatrix_inverse_right_apply S hS)

theorem innerMatrixEquiv_toCLM (S : Matrix ι ι ℝ) (hS : IsUnit S) :
    (innerMatrixEquiv S hS : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S := by
  unfold innerMatrixEquiv
  exact ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse _ _ _ _

theorem innerMatrixEquiv_symm_toCLM (S : Matrix ι ι ℝ) (hS : IsUnit S) :
    ((innerMatrixEquiv S hS).symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S⁻¹ := by
  unfold innerMatrixEquiv
  rw [ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse]

theorem innerMatrixEquiv_weight_toCLM (Ω : Matrix ι ι ℝ) (hΩ : IsUnit Ω) (sign : Bool) :
    (innerHilbertWeight (innerMatrixEquiv Ω hΩ) sign :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (innerInterfaceWeight Ω sign) := by
  cases sign with
  | false => exact innerMatrixEquiv_symm_toCLM Ω hΩ
  | true => exact innerMatrixEquiv_toCLM Ω hΩ

theorem innerInterfaceWeight_inv_eq_not (Ω : Matrix ι ι ℝ) (hΩ : IsUnit Ω) (sign : Bool) :
    (innerInterfaceWeight Ω sign)⁻¹ = innerInterfaceWeight Ω (!sign) := by
  cases sign with
  | false => exact Matrix.nonsing_inv_nonsing_inv Ω ((Matrix.isUnit_iff_isUnit_det Ω).mp hΩ)
  | true => rfl

theorem innerMatrixCLM_selfAdjoint (S : Matrix ι ι ℝ) (hS : S.IsHermitian) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S) := by
  have h : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S).adjoint =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S := by
    rw [← innerMatrix_toEuclideanCLM_conjTranspose, hS.eq]
  exact h

variable (S₀ Ω E : Matrix ι ι ℝ)
  (hS₀ : S₀.PosDef) (hΩ : Ω.PosDef) (hcomm : Commute Ω S₀)
  (hsmall : ∀ sign : Bool,
    ‖innerInterfaceWeightedError S₀ (innerInterfaceWeight Ω sign) E‖ < 1 / 2)

/-- The actual Neumann middle operator for each weight sign. -/
def innerInterfaceHilbertNeumann (sign : Bool) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
    (innerInterfaceNeumann (innerInterfaceWeightedError S₀ (innerInterfaceWeight Ω sign) E)
      (hsmall sign))

theorem innerInterfaceHilbertNeumann_norm_le (sign : Bool) :
    ‖innerInterfaceHilbertNeumann S₀ Ω E hsmall sign‖ ≤ 2 := by
  rw [innerInterfaceHilbertNeumann, Matrix.l2_opNorm_toEuclideanCLM]
  exact norm_innerInterfaceNeumann_le_two _ _

include hS₀ hcomm in
/-- The matrix formula is the exact operator factorization required by
the opposite-sign-adjoint estimate for the Poisson correction. -/
theorem innerInterfaceHilbert_factorization (sign : Bool) :
    (innerHilbertWeight (innerMatrixEquiv Ω hΩ.isUnit) sign :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) ∘L
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (S₀ + E)⁻¹ ∘L
      (innerHilbertWeight (innerMatrixEquiv Ω hΩ.isUnit) (!sign) :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (innerInterfaceInverseSqrt S₀) ∘L
      innerInterfaceHilbertNeumann S₀ Ω E hsmall sign ∘L
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (innerInterfaceInverseSqrt S₀) := by
  have h := (innerInterface_inverse_both_weights S₀ Ω E hS₀ hΩ hcomm hsmall).2 sign
  have hmap := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) h.1
  simpa only [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
    innerInterfaceWeight_inv_eq_not Ω hΩ.isUnit, innerMatrixEquiv_weight_toCLM,
    innerInterfaceHilbertNeumann] using hmap

section PhysicalCorrection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

include hS₀ hcomm hsmall in
/-- The correction estimate follows directly from the actual matrix
smallness and the two Poisson bounds. No separate inverse factorization
or Neumann-norm premise remains. -/
theorem innerCoupling_bound_from_interface (W : H ≃L[ℝ] H)
    (T : EuclideanSpace ℝ ι →L[ℝ] H)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H)) {C j : ℝ} (hC : 0 ≤ C) (hj : 0 < j)
    (hP : ∀ sign : Bool,
      ‖innerWeightedPoisson W (innerMatrixEquiv Ω hΩ.isUnit) T
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (innerInterfaceInverseSqrt S₀)) sign‖ ≤ C / j)
    (sign : Bool) :
    ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
        innerCouplingCorrection T (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (S₀ + E)⁻¹) ∘L
        (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤ 2 * C ^ 2 / j ^ 2 := by
  have hweight : IsSelfAdjoint (innerMatrixEquiv Ω hΩ.isUnit :
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) := by
    rw [innerMatrixEquiv_toCLM]
    exact innerMatrixCLM_selfAdjoint Ω hΩ.isHermitian
  exact innerCoupling_weighted_bound W (innerMatrixEquiv Ω hΩ.isUnit) T _ _
    (innerInterfaceHilbertNeumann S₀ Ω E hsmall) hW hweight
    (innerMatrixCLM_selfAdjoint _ (innerInterfaceInverseSqrt_isHermitian S₀))
    (innerInterfaceHilbert_factorization S₀ Ω E hS₀ hΩ hcomm hsmall)
    hC hj hP (innerInterfaceHilbertNeumann_norm_le S₀ Ω E hsmall) sign

end PhysicalCorrection

end ContinuousFlexibility.Radial
