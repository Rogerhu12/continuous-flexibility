import ContinuousFlexibility.Radial.InnerInterfaceInverse
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Contractive normalization by the full inner reference interface

The diagonal cut energy is dominated by the full reference interface,
which also contains the positive gap Dirichlet-to-Neumann blocks. This
energy comparison implies the contraction used in the bounded-overlap
estimate. All norms are the real Euclidean operator norms, in arbitrary
finite boundary dimension.

The proof uses the positive quadratic form on the real Hilbert space;
it does not require a complex C⋆-algebra structure or assume the desired
contraction. The matrix and continuous-operator adjoints agree exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix conjugate transpose is the adjoint on the same real
Euclidean boundary space. -/
theorem innerMatrix_toEuclideanCLM_conjTranspose (A : Matrix ι ι ℝ) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Aᴴ =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).adjoint := by
  calc
    _ = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (star A) :=
      congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))
        (Matrix.star_eq_conjTranspose A).symm
    _ = star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) :=
      map_star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A
    _ = _ := ContinuousLinearMap.star_eq_adjoint _

/-- A quadratic-form contraction gives an operator-norm contraction on
real Euclidean space, including the empty boundary case. -/
theorem innerMatrix_norm_le_one_of_conjTranspose_mul_le_one
    (A : Matrix ι ι ℝ) (hA : Aᴴ * A ≤ 1) : ‖A‖ ≤ 1 := by
  have hpositive :
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 - Aᴴ * A)).IsPositive := by
    apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hA)
  have hpositive' :
      (1 - (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).adjoint *
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).IsPositive := by
    simpa only [map_sub, map_one, map_mul,
      innerMatrix_toEuclideanCLM_conjTranspose] using hpositive
  suffices hnorm : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A‖ ≤ 1 by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hnorm
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hx := hpositive'.inner_nonneg_right x
  simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq] at hx
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_nonneg.mp hx)

/-- The inverse square root is Hermitian in the same matrix algebra. -/
theorem innerInterfaceInverseSqrt_isHermitian (S₀ : Matrix ι ι ℝ) :
    (innerInterfaceInverseSqrt S₀).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S₀⁻¹)).isHermitian

/-- The cut-energy normalization appearing on the left of every assembled
local error block. -/
def innerReferenceNormalization (S₀ D : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  innerInterfaceInverseSqrt S₀ * CFC.sqrt D

/-- The right normalization is exactly the adjoint of the left one. -/
theorem innerReferenceNormalization_conjTranspose (S₀ D : Matrix ι ι ℝ) :
    (innerReferenceNormalization S₀ D)ᴴ =
      CFC.sqrt D * innerInterfaceInverseSqrt S₀ := by
  have hD : (CFC.sqrt D).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian
  dsimp only [innerReferenceNormalization]
  rw [Matrix.conjTranspose_mul, hD.eq,
    (innerInterfaceInverseSqrt_isHermitian S₀).eq]

/-- The square of the normalization records exactly the conjugated cut
energy, without dropping any gap contribution from the reference. -/
theorem innerReferenceNormalization_mul_conjTranspose
    (S₀ D : Matrix ι ι ℝ) (hD : D.PosSemidef) :
    innerReferenceNormalization S₀ D * (innerReferenceNormalization S₀ D)ᴴ =
      innerInterfaceInverseSqrt S₀ * D * innerInterfaceInverseSqrt S₀ := by
  rw [innerReferenceNormalization_conjTranspose]
  dsimp only [innerReferenceNormalization]
  calc
    (innerInterfaceInverseSqrt S₀ * CFC.sqrt D) *
        (CFC.sqrt D * innerInterfaceInverseSqrt S₀) =
      innerInterfaceInverseSqrt S₀ * (CFC.sqrt D * CFC.sqrt D) *
        innerInterfaceInverseSqrt S₀ := by noncomm_ring
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self D hD.nonneg]

/-- Conjugating the energy comparison by the inverse square root gives
the identity upper bound. -/
theorem innerReference_normalized_energy_le_one
    (S₀ D : Matrix ι ι ℝ) (hS₀ : S₀.PosDef) (hle : D ≤ S₀) :
    innerInterfaceInverseSqrt S₀ * D * innerInterfaceInverseSqrt S₀ ≤ 1 := by
  calc
    _ ≤ innerInterfaceInverseSqrt S₀ * S₀ * innerInterfaceInverseSqrt S₀ := by
      simpa only [innerInterfaceInverseSqrt, CFC.conjSqrt_apply] using
        (CFC.conjSqrt_monotone (c := S₀⁻¹) hle)
    _ = 1 := innerInterfaceInverseSqrt_normalizes S₀ hS₀

/-- The reference normalization is contractive as a consequence of
`0 ≤ D ≤ S₀` and strict positivity of the full reference interface. -/
theorem norm_innerReferenceNormalization_le_one
    (S₀ D : Matrix ι ι ℝ) (hS₀ : S₀.PosDef) (hD : D.PosSemidef)
    (hle : D ≤ S₀) : ‖innerReferenceNormalization S₀ D‖ ≤ 1 := by
  have henergy := innerReference_normalized_energy_le_one S₀ D hS₀ hle
  have hcontraction := innerMatrix_norm_le_one_of_conjTranspose_mul_le_one
    (innerReferenceNormalization S₀ D)ᴴ (by
      simpa only [Matrix.conjTranspose_conjTranspose,
        innerReferenceNormalization_mul_conjTranspose S₀ D hD] using henergy)
  simpa only [Matrix.l2_opNorm_conjTranspose] using hcontraction

/-- The reverse product has the same contraction bound because it is the
adjoint, not because the two square roots commute. -/
theorem norm_innerReferenceNormalization_right_le_one
    (S₀ D : Matrix ι ι ℝ) (hS₀ : S₀.PosDef) (hD : D.PosSemidef)
    (hle : D ≤ S₀) : ‖CFC.sqrt D * innerInterfaceInverseSqrt S₀‖ ≤ 1 := by
  rw [← innerReferenceNormalization_conjTranspose,
    Matrix.l2_opNorm_conjTranspose]
  exact norm_innerReferenceNormalization_le_one S₀ D hS₀ hD hle

/-- Exact compatibility with the Hilbert adjoint used in the assembled
error and Poisson estimates. -/
theorem innerReferenceNormalization_toEuclideanCLM_adjoint
    (S₀ D : Matrix ι ι ℝ) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (innerReferenceNormalization S₀ D)).adjoint =
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
          (CFC.sqrt D * innerInterfaceInverseSqrt S₀) := by
  rw [← innerMatrix_toEuclideanCLM_conjTranspose,
    innerReferenceNormalization_conjTranspose]

/-- The matrix-to-Hilbert-space conversion has no loss in the contraction
constant. -/
theorem norm_innerReferenceNormalization_toEuclideanCLM_le_one
    (S₀ D : Matrix ι ι ℝ) (hS₀ : S₀.PosDef) (hD : D.PosSemidef)
    (hle : D ≤ S₀) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (innerReferenceNormalization S₀ D)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact norm_innerReferenceNormalization_le_one S₀ D hS₀ hD hle

/-- The functional-calculus square root of the diagonal cut energy is
the coordinatewise positive square root. -/
theorem innerReference_diagonal_sqrt (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    CFC.sqrt (Matrix.diagonal κ) = Matrix.diagonal (fun i => Real.sqrt (κ i)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    simpa only [pow_two] using Real.sq_sqrt (hκ i)
  · exact (Matrix.posSemidef_diagonal_iff.mpr (fun i => Real.sqrt_nonneg (κ i))).nonneg

section GapAssembly

variable {β : Type*} [Fintype β]

/-- Strictly positive cut energies and positive semidefinite gap blocks
give strict positivity of the full reference matrix. -/
theorem innerReference_posDef_of_psd_gaps
    (κ : ι → ℝ) (Γ : β → Matrix ι ι ℝ)
    (hκ : ∀ i, 0 < κ i) (hΓ : ∀ b, (Γ b).PosSemidef) :
    (Matrix.diagonal κ + ∑ b, Γ b).PosDef :=
  (Matrix.posDef_diagonal_iff.mpr hκ).add_posSemidef
    (Matrix.posSemidef_sum Finset.univ (fun b _ => hΓ b))

/-- Keeping every positive gap block can only increase the cut energy. -/
theorem innerReference_diagonal_le_of_psd_gaps
    (κ : ι → ℝ) (Γ : β → Matrix ι ι ℝ)
    (hΓ : ∀ b, (Γ b).PosSemidef) :
    Matrix.diagonal κ ≤ Matrix.diagonal κ + ∑ b, Γ b :=
  le_add_of_nonneg_right (Matrix.posSemidef_sum Finset.univ (fun b _ => hΓ b)).nonneg

/-- Local gap matrices may have different boundary dimensions. Their
actual restrictions lift positivity to the global cut space. -/
theorem innerReference_posDef_of_local_gaps
    {ν : β → Type*} [∀ b, Fintype (ν b)]
    (κ : ι → ℝ) (Λ : ∀ b, Matrix (ν b) (ν b) ℝ)
    (R : ∀ b, Matrix (ν b) ι ℝ)
    (hκ : ∀ i, 0 < κ i) (hΛ : ∀ b, (Λ b).PosSemidef) :
    (Matrix.diagonal κ + ∑ b, (R b)ᴴ * Λ b * R b).PosDef ∧
      Matrix.diagonal κ ≤ Matrix.diagonal κ + ∑ b, (R b)ᴴ * Λ b * R b := by
  have hΓ (b : β) : ((R b)ᴴ * Λ b * R b).PosSemidef :=
    (hΛ b).conjTranspose_mul_mul_same (R b)
  exact ⟨innerReference_posDef_of_psd_gaps κ _ hκ hΓ,
    innerReference_diagonal_le_of_psd_gaps κ _ hΓ⟩

/-- In the assembled reference the contraction follows directly from
positive cut energies and the positive gap blocks. -/
theorem norm_innerReferenceNormalization_of_psd_gaps_le_one
    (κ : ι → ℝ) (Γ : β → Matrix ι ι ℝ)
    (hκ : ∀ i, 0 < κ i) (hΓ : ∀ b, (Γ b).PosSemidef) :
    ‖innerReferenceNormalization (Matrix.diagonal κ + ∑ b, Γ b)
      (Matrix.diagonal κ)‖ ≤ 1 :=
  norm_innerReferenceNormalization_le_one _ _
    (innerReference_posDef_of_psd_gaps κ Γ hκ hΓ)
    (Matrix.posDef_diagonal_iff.mpr hκ).posSemidef
    (innerReference_diagonal_le_of_psd_gaps κ Γ hΓ)

end GapAssembly

end ContinuousFlexibility.Radial
