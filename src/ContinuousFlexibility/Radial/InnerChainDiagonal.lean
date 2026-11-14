module

public import ContinuousFlexibility.Radial.InnerChainBoundaryHilbert
public import ContinuousFlexibility.Radial.InnerReferenceNormalization

/-!
# Diagonal multiplication on the actual chain cut space

The same endpoint restrictions used by weak gluing intertwine physical
cut weights and cut energies with their two-endpoint diagonal maps.
Outer endpoint values are zero, so an arbitrary positive outer diagonal
value introduces no boundary degree of freedom.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Multiplication by a scalar on each internal cut, in the Euclidean
boundary representation used by the full reference matrix. -/
def innerBoundaryDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (Matrix.diagonal a)

theorem innerBoundaryDiagonal_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ξ : EuclideanSpace ℝ ι) (i : ι) :
    innerBoundaryDiagonal a ξ i = a i * ξ i := by
  simpa only [innerBoundaryDiagonal, Matrix.mulVec_diagonal] using
    congrFun (Matrix.ofLp_toEuclideanCLM (Matrix.diagonal a) ξ) i

def innerChainScalarRestriction (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (outer : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then
    if hp : 0 < p.val then a ⟨p.val - 1, by omega⟩ else outer
  else
    if hp : p.val < n then a ⟨p.val, hp⟩ else outer

theorem innerChainScalarRestriction_pos (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) {outer : ℝ} (ha : ∀ i, 0 < a i) (ho : 0 < outer) (i : Fin 2) :
    0 < innerChainScalarRestriction n p a outer i := by
  unfold innerChainScalarRestriction
  split_ifs <;> first | exact ho | exact ha _

theorem innerChainScalarRestriction_map (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (outer : ℝ) (f : ℝ → ℝ) (i : Fin 2) :
    innerChainScalarRestriction n p (fun k => f (a k)) (f outer) i =
      f (innerChainScalarRestriction n p a outer i) := by
  unfold innerChainScalarRestriction
  split_ifs <;> rfl

/-- Internal cut multiplication is exactly the local two-endpoint
multiplication. The two exterior Dirichlet values stay zero. -/
theorem innerChainBoundaryCLM_diagonal (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (outer : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    innerChainBoundaryCLM n p (innerBoundaryDiagonal a ξ) =
      WithLp.toLp 2 (fun i => innerChainScalarRestriction n p a outer i *
        innerChainBoundaryCLM n p ξ i) := by
  apply PiLp.ext
  intro i
  simp only [innerChainBoundaryCLM_apply, innerChainBoundaryRestriction_apply,
    PiLp.toLp_apply, innerChainScalarRestriction]
  split_ifs <;> simp only [innerBoundaryDiagonal_apply, mul_zero]

theorem innerChainBoundaryCLM_inverse_diagonal (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    innerChainBoundaryCLM n p (innerBoundaryDiagonal (fun i => (a i)⁻¹) ξ) =
      WithLp.toLp 2 (fun i => (innerChainScalarRestriction n p a 1 i)⁻¹ *
        innerChainBoundaryCLM n p ξ i) := by
  rw [innerChainBoundaryCLM_diagonal n p (fun i => (a i)⁻¹) ((1 : ℝ)⁻¹)]
  simp only [innerChainScalarRestriction_map]

theorem innerChainBoundaryCLM_sqrt_diagonal (n : ℕ) (p : Fin (n + 1))
    (a : Fin n → ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    innerChainBoundaryCLM n p (innerBoundaryDiagonal (fun i => Real.sqrt (a i)) ξ) =
      WithLp.toLp 2 (fun i => Real.sqrt (innerChainScalarRestriction n p a 1 i) *
        innerChainBoundaryCLM n p ξ i) := by
  rw [innerChainBoundaryCLM_diagonal n p (fun i => Real.sqrt (a i)) (Real.sqrt 1)]
  simp only [innerChainScalarRestriction_map]

/-- Normalizing the global cut energies by the full positive reference
is contractive even though the two matrices need not commute. -/
theorem innerBoundaryDiagonal_sqrt_reference_norm_le_one (n : ℕ)
    (κ : Fin n → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (S₀ : Matrix (Fin n) (Fin n) ℝ) (hS₀ : S₀.PosDef)
    (hdom : Matrix.diagonal κ ≤ S₀) :
    ‖innerBoundaryDiagonal (fun i => Real.sqrt (κ i)) ∘L
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (innerInterfaceInverseSqrt S₀)‖ ≤ 1 := by
  have h := norm_innerReferenceNormalization_right_le_one S₀ (Matrix.diagonal κ)
    hS₀ (Matrix.posSemidef_diagonal_iff.mpr hκ) hdom
  rw [innerReference_diagonal_sqrt κ hκ] at h
  have h' := h
  rw [← Matrix.l2_opNorm_toEuclideanCLM, map_mul] at h'
  exact h'

end ContinuousFlexibility.Radial
