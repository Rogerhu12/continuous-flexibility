module

public import ContinuousFlexibility.Radial.InnerChainDiagonal
public import ContinuousFlexibility.Radial.InnerTwoCutError

/-!
# The actual chain error and its physical cut normalization

This module keeps one error operator: the sum of the two-endpoint model
errors extended by the same endpoint restrictions used by weak gluing.
Diagonal cut weights and energy normalization are moved through those
restrictions exactly. The estimate therefore applies to the actual
conjugated interface error, with no global weight condition number.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

theorem innerBoundaryDiagonal_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) : (innerBoundaryDiagonal a).adjoint = innerBoundaryDiagonal a := by
  simp only [innerBoundaryDiagonal, ← innerMatrix_toEuclideanCLM_conjTranspose,
    (Matrix.isHermitian_diagonal a).eq]

theorem innerBoundaryDiagonal_selfAdjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) : IsSelfAdjoint (innerBoundaryDiagonal a) :=
  innerBoundaryDiagonal_adjoint a

theorem innerBoundaryDiagonal_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) :
    innerBoundaryDiagonal a ∘L innerBoundaryDiagonal b =
      innerBoundaryDiagonal (fun i => a i * b i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  simp only [ContinuousLinearMap.comp_apply, innerBoundaryDiagonal_apply]
  ring

theorem innerChainBoundaryCLM_diagonal_intertwine (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (outer : ℝ) :
    innerChainBoundaryCLM n p ∘L innerBoundaryDiagonal a =
      innerBoundaryDiagonal (innerChainScalarRestriction n p a outer) ∘L
        innerChainBoundaryCLM n p := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [ContinuousLinearMap.comp_apply, innerChainBoundaryCLM_diagonal n p a outer]
  apply PiLp.ext
  intro i
  simp only [PiLp.toLp_apply, innerBoundaryDiagonal_apply]

theorem innerChainBoundaryCLM_diagonal_adjoint (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (outer : ℝ) :
    innerBoundaryDiagonal a ∘L (innerChainBoundaryCLM n p).adjoint =
      (innerChainBoundaryCLM n p).adjoint ∘L
        innerBoundaryDiagonal (innerChainScalarRestriction n p a outer) := by
  have h := congrArg ContinuousLinearMap.adjoint
    (innerChainBoundaryCLM_diagonal_intertwine n p a outer)
  simpa only [ContinuousLinearMap.adjoint_comp, innerBoundaryDiagonal_adjoint] using h

/-- Pulling two diagonals through the sum uses the same actual endpoint
restriction on each side of each local block. -/
theorem innerChainBlockSum_diagonal (n : ℕ)
    (E : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : Fin n → ℝ) (a₀ b₀ : ℝ) :
    innerBoundaryDiagonal a ∘L innerInterfaceBlockSum (innerChainBoundaryCLM n) E ∘L
        innerBoundaryDiagonal b =
      innerInterfaceBlockSum (innerChainBoundaryCLM n) (fun p =>
        innerBoundaryDiagonal (innerChainScalarRestriction n p a a₀) ∘L E p ∘L
          innerBoundaryDiagonal (innerChainScalarRestriction n p b b₀)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℝ
  intro η
  simp only [ContinuousLinearMap.comp_apply]
  have hsym :
      ⟪innerBoundaryDiagonal a
        (innerInterfaceBlockSum (innerChainBoundaryCLM n) E (innerBoundaryDiagonal b ξ)), η⟫_ℝ =
      ⟪innerInterfaceBlockSum (innerChainBoundaryCLM n) E (innerBoundaryDiagonal b ξ),
        innerBoundaryDiagonal a η⟫_ℝ :=
    (innerBoundaryDiagonal_selfAdjoint a).isSymmetric _ _
  rw [hsym, innerInterfaceBlockSum_inner, innerInterfaceBlockSum_inner]
  apply Finset.sum_congr rfl
  intro p _
  have ha := congrArg (fun A => A η)
    (innerChainBoundaryCLM_diagonal_intertwine n p a a₀)
  have hb := congrArg (fun A => A ξ)
    (innerChainBoundaryCLM_diagonal_intertwine n p b b₀)
  simp only [ContinuousLinearMap.comp_apply] at ha hb ⊢
  rw [ha, hb]
  exact ((innerBoundaryDiagonal_selfAdjoint
    (innerChainScalarRestriction n p a a₀)).isSymmetric _ _).symm

/-- The global error is made from the actual local flux errors. -/
def innerChainErrorMatrix (n : ℕ)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm
    (innerInterfaceBlockSum (innerChainBoundaryCLM n)
      (fun p => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (E p)))

theorem innerChainErrorMatrix_toEuclideanCLM (n : ℕ)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (innerChainErrorMatrix n E) =
      innerInterfaceBlockSum (innerChainBoundaryCLM n)
        (fun p => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (E p)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _

/-- Entry normalization agrees exactly with multiplication by the two
physical diagonals, including both reciprocal weight signs. -/
theorem innerTwoCutWeightedError_diagonal (κ w : Fin 2 → ℝ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (sign : Bool) :
    innerTwoCutWeightedError κ w E sign =
      Matrix.diagonal (fun i => (if sign then w i else (w i)⁻¹) / Real.sqrt (κ i)) *
        E * Matrix.diagonal
          (fun i => (if sign then (w i)⁻¹ else w i) / Real.sqrt (κ i)) := by
  ext i k
  simp only [innerTwoCutWeightedError, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Real.sqrt_mul (hκ i).le]
  cases sign <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    field_simp [(hw i).ne', (hw k).ne', (Real.sqrt_pos.mpr (hκ i)).ne',
      (Real.sqrt_pos.mpr (hκ k)).ne'] <;> ring

theorem innerChainScalarRestriction_weighted_energy (n : ℕ) (p : Fin (n + 1))
    (w κ : Fin n → ℝ) (inverse : Bool) (i : Fin 2) :
    innerChainScalarRestriction n p
      (fun k => (if inverse then (w k)⁻¹ else w k) / Real.sqrt (κ k)) 1 i =
      (if inverse then (innerChainScalarRestriction n p w 1 i)⁻¹
        else innerChainScalarRestriction n p w 1 i) /
          Real.sqrt (innerChainScalarRestriction n p κ 1 i) := by
  unfold innerChainScalarRestriction
  split_ifs <;> simp only [Real.sqrt_one, inv_one, div_one]

/-- The cut-energy normalized conjugate of the actual global error. -/
def innerChainEnergyErrorMatrix (n : ℕ) (κ w : Fin n → ℝ)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => w i / Real.sqrt (κ i)) * innerChainErrorMatrix n E *
    Matrix.diagonal (fun i => (w i)⁻¹ / Real.sqrt (κ i))

theorem innerChainEnergyErrorMatrix_toEuclideanCLM (n : ℕ) (κ w : Fin n → ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (innerChainEnergyErrorMatrix n κ w E) =
      innerInterfaceBlockSum (innerChainBoundaryCLM n) (fun p =>
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          (innerTwoCutWeightedError (innerChainScalarRestriction n p κ 1)
            (innerChainScalarRestriction n p w 1) (E p) true)) := by
  simp only [innerChainEnergyErrorMatrix, map_mul, ContinuousLinearMap.mul_def,
    innerChainErrorMatrix_toEuclideanCLM, ContinuousLinearMap.comp_assoc]
  rw [show Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (Matrix.diagonal (fun i => w i / Real.sqrt (κ i))) =
        innerBoundaryDiagonal (fun i => w i / Real.sqrt (κ i)) from rfl,
    show Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (Matrix.diagonal (fun i => (w i)⁻¹ / Real.sqrt (κ i))) =
        innerBoundaryDiagonal (fun i => (w i)⁻¹ / Real.sqrt (κ i)) from rfl]
  rw [innerChainBlockSum_diagonal n _ _ _ 1 1]
  apply congrArg (innerInterfaceBlockSum (innerChainBoundaryCLM n))
  funext p
  rw [innerTwoCutWeightedError_diagonal _ _ (E p)
    (innerChainScalarRestriction_pos n p κ hκ (by norm_num))
    (innerChainScalarRestriction_pos n p w hw (by norm_num)) true]
  simp only [ite_true, map_mul, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc, innerBoundaryDiagonal]
  have hleft : innerChainScalarRestriction n p (fun k => w k / Real.sqrt (κ k)) 1 =
      fun i => innerChainScalarRestriction n p w 1 i /
        Real.sqrt (innerChainScalarRestriction n p κ 1 i) := by
    funext i
    simpa only [Bool.false_eq_true, ite_false] using
      innerChainScalarRestriction_weighted_energy n p w κ false i
  have hright : innerChainScalarRestriction n p (fun k => (w k)⁻¹ / Real.sqrt (κ k)) 1 =
      fun i => (innerChainScalarRestriction n p w 1 i)⁻¹ /
        Real.sqrt (innerChainScalarRestriction n p κ 1 i) := by
    funext i
    simpa only [ite_true] using innerChainScalarRestriction_weighted_energy n p w κ true i
  rw [hleft, hright]

/-- Each internal cut is counted at most twice. -/
theorem innerChainEnergyErrorMatrix_norm_le (n : ℕ) (κ w : Fin n → ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hE : ∀ p, ‖innerTwoCutWeightedError (innerChainScalarRestriction n p κ 1)
      (innerChainScalarRestriction n p w 1) (E p) true‖ ≤ η) :
    ‖innerChainEnergyErrorMatrix n κ w E‖ ≤ 2 * η := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM,
    innerChainEnergyErrorMatrix_toEuclideanCLM n κ w hκ hw E]
  exact norm_innerChainBoundaryBlockSum_le n _ hη (fun p => by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hE p)

theorem innerBoundaryWeightMatrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    (Matrix.diagonal w)⁻¹ = Matrix.diagonal (fun i => (w i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have heq : (fun i => w i * (w i)⁻¹) = (fun _ : ι => (1 : ℝ)) := by
    funext i
    exact mul_inv_cancel₀ (hw i)
  rw [heq, Matrix.diagonal_one]

/-- The actual inverse square root normalization factors through the
contractive full-reference cut-energy normalization on both sides. -/
theorem innerChainErrorMatrix_reference_factorization (n : ℕ)
    (S₀ : Matrix (Fin n) (Fin n) ℝ) (κ w : Fin n → ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) :
    innerInterfaceWeightedError S₀ (Matrix.diagonal w) (innerChainErrorMatrix n E) =
      innerReferenceNormalization S₀ (Matrix.diagonal κ) *
        innerChainEnergyErrorMatrix n κ w E *
          (innerReferenceNormalization S₀ (Matrix.diagonal κ))ᴴ := by
  let R := Matrix.diagonal (fun i => Real.sqrt (κ i))
  let A := Matrix.diagonal (fun i => w i / Real.sqrt (κ i))
  let B := Matrix.diagonal (fun i => (w i)⁻¹ / Real.sqrt (κ i))
  have hleft : R * A = Matrix.diagonal w := by
    rw [show R = Matrix.diagonal (fun i => Real.sqrt (κ i)) from rfl,
      show A = Matrix.diagonal (fun i => w i / Real.sqrt (κ i)) from rfl,
      Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    field_simp [(Real.sqrt_pos.mpr (hκ i)).ne']
  have hright : B * R = Matrix.diagonal (fun i => (w i)⁻¹) := by
    rw [show R = Matrix.diagonal (fun i => Real.sqrt (κ i)) from rfl,
      show B = Matrix.diagonal (fun i => (w i)⁻¹ / Real.sqrt (κ i)) from rfl,
      Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    field_simp [(Real.sqrt_pos.mpr (hκ i)).ne']
  rw [innerInterfaceWeightedError, innerBoundaryWeightMatrix_inv w (fun i => (hw i).ne'),
    innerReferenceNormalization_conjTranspose, innerReferenceNormalization,
    innerReference_diagonal_sqrt κ (fun i => (hκ i).le)]
  change innerInterfaceInverseSqrt S₀ *
      (Matrix.diagonal w * innerChainErrorMatrix n E * Matrix.diagonal (fun i => (w i)⁻¹)) *
      innerInterfaceInverseSqrt S₀ =
    (innerInterfaceInverseSqrt S₀ * R) * (A * innerChainErrorMatrix n E * B) *
      (R * innerInterfaceInverseSqrt S₀)
  rw [← hleft, ← hright]
  noncomm_ring

/-- This is the strict one-half estimate for the actual assembled
interface error. Local estimates may come from either weight sign. -/
theorem innerChainErrorMatrix_normalized_lt_half (n : ℕ)
    (S₀ : Matrix (Fin n) (Fin n) ℝ) (κ w : Fin n → ℝ)
    (hS₀ : S₀.PosDef) (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (hdom : Matrix.diagonal κ ≤ S₀)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (hE : ∀ p, ‖innerTwoCutWeightedError (innerChainScalarRestriction n p κ 1)
      (innerChainScalarRestriction n p w 1) (E p) true‖ ≤ η) :
    ‖innerInterfaceWeightedError S₀ (Matrix.diagonal w) (innerChainErrorMatrix n E)‖ < 1 / 2 := by
  have hA := norm_innerReferenceNormalization_le_one S₀ (Matrix.diagonal κ) hS₀
    (Matrix.posSemidef_diagonal_iff.mpr (fun i => (hκ i).le)) hdom
  have hAstar : ‖(innerReferenceNormalization S₀ (Matrix.diagonal κ))ᴴ‖ ≤ 1 := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using hA
  have hblock := innerChainEnergyErrorMatrix_norm_le n κ w hκ hw E hη hE
  rw [innerChainErrorMatrix_reference_factorization n S₀ κ w hκ hw E]
  have hnorm : ‖innerReferenceNormalization S₀ (Matrix.diagonal κ) *
      innerChainEnergyErrorMatrix n κ w E *
      (innerReferenceNormalization S₀ (Matrix.diagonal κ))ᴴ‖ ≤ 2 * η := by
    calc
      _ ≤ (‖innerReferenceNormalization S₀ (Matrix.diagonal κ)‖ *
          ‖innerChainEnergyErrorMatrix n κ w E‖) *
          ‖(innerReferenceNormalization S₀ (Matrix.diagonal κ))ᴴ‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * (2 * η)) * 1 :=
        mul_le_mul (mul_le_mul hA hblock (norm_nonneg _) zero_le_one)
          hAstar (norm_nonneg _) (by positivity)
      _ = 2 * η := by ring
  exact hnorm.trans_lt (by linarith only [hηsmall])

theorem innerTwoCutWeightedError_signed (κ w : Fin 2 → ℝ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) (hw : ∀ i, 0 < w i) (sign : Bool) :
    innerTwoCutWeightedError κ (fun i => if sign then w i else (w i)⁻¹) E true =
      innerTwoCutWeightedError κ w E sign := by
  ext i k
  cases sign with
  | true => simp only [innerTwoCutWeightedError, ite_true]
  | false =>
    simp only [innerTwoCutWeightedError, ite_true, Bool.false_eq_true, ite_false]
    congr 1
    field_simp [(hw i).ne', (hw k).ne']

/-- Both estimates concern the same physical error and the canonical
inverse of the same positive diagonal cut weight. -/
theorem innerChainErrorMatrix_normalized_both (n : ℕ)
    (S₀ : Matrix (Fin n) (Fin n) ℝ) (κ w : Fin n → ℝ)
    (hS₀ : S₀.PosDef) (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (hdom : Matrix.diagonal κ ≤ S₀)
    (E : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (hE : ∀ p sign, ‖innerTwoCutWeightedError (innerChainScalarRestriction n p κ 1)
      (innerChainScalarRestriction n p w 1) (E p) sign‖ ≤ η) (sign : Bool) :
    ‖innerInterfaceWeightedError S₀ (innerInterfaceWeight (Matrix.diagonal w) sign)
      (innerChainErrorMatrix n E)‖ < 1 / 2 := by
  let v : Fin n → ℝ := fun i => if sign then w i else (w i)⁻¹
  have hv : ∀ i, 0 < v i := by
    intro i
    dsimp only [v]
    split_ifs
    · exact hw i
    · exact inv_pos.mpr (hw i)
  have hweight : innerInterfaceWeight (Matrix.diagonal w) sign = Matrix.diagonal v := by
    cases sign with
    | true => simp only [innerInterfaceWeight, ite_true, v]
    | false =>
      simpa only [innerInterfaceWeight, Bool.false_eq_true, ite_false, v] using
        innerBoundaryWeightMatrix_inv w (fun i => (hw i).ne')
  rw [hweight]
  apply innerChainErrorMatrix_normalized_lt_half n S₀ κ v hS₀ hκ hv hdom E hη hηsmall
  intro p
  have hlocal : innerChainScalarRestriction n p v 1 =
      fun i => if sign then innerChainScalarRestriction n p w 1 i
        else (innerChainScalarRestriction n p w 1 i)⁻¹ := by
    funext i
    simpa only [v, inv_one, ite_self] using
      innerChainScalarRestriction_map n p w 1 (fun x => if sign then x else x⁻¹) i
  rw [hlocal, innerTwoCutWeightedError_signed _ _ _
    (innerChainScalarRestriction_pos n p w hw (by norm_num)) sign]
  exact hE p sign

end ContinuousFlexibility.Radial
