import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Exact transfer through the physical isometric inclusion

These lemmas transfer operator bounds, Hilbert adjoints, and weighted
Schur formulas through an actual isometric inclusion. They introduce
no norm-equivalence constants.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace

section NormTransfer

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace ℝ E] [NormedSpace ℝ F]
  [NormedSpace ℝ X] [NormedSpace ℝ Y]

theorem innerIsometricOperator_norm_le
    (i : E →ₗᵢ[ℝ] X) (k : F →ₗᵢ[ℝ] Y)
    (A : E →L[ℝ] F) (A0 : X →L[ℝ] Y)
    (hA : ∀ x, k (A x) = A0 (i x)) : ‖A‖ ≤ ‖A0‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A0)
  intro x
  calc
    ‖A x‖ = ‖k (A x)‖ := (k.norm_map _).symm
    _ = ‖A0 (i x)‖ := congrArg norm (hA x)
    _ ≤ ‖A0‖ * ‖i x‖ := A0.le_opNorm _
    _ = ‖A0‖ * ‖x‖ := by rw [i.norm_map]

end NormTransfer

section Endomorphisms

variable {H E : Type*} [NormedAddCommGroup H] [NormedAddCommGroup E]
  [NormedSpace ℝ H] [NormedSpace ℝ E]

/-- Both weight directions and the output coefficient multiplier retain
the ambient estimate on the same supported physical Hilbert space. -/
theorem innerIsometricWeightedOperator_norm_le
    (i : H →ₗᵢ[ℝ] E)
    (A W Winv C : H →L[ℝ] H) (A0 W0 Winv0 C0 : E →L[ℝ] E)
    (hA : ∀ x, i (A x) = A0 (i x))
    (hW : ∀ x, i (W x) = W0 (i x))
    (hWinv : ∀ x, i (Winv x) = Winv0 (i x))
    (hC : ∀ x, i (C x) = C0 (i x)) :
    ‖C.comp (W.comp (A.comp Winv))‖ ≤ ‖C0.comp (W0.comp (A0.comp Winv0))‖ := by
  apply innerIsometricOperator_norm_le i i
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  rw [hC, hW, hA, hWinv]

end Endomorphisms

section HilbertTransfer

variable {B H E : Type*}
  [NormedAddCommGroup B] [NormedAddCommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℝ B] [InnerProductSpace ℝ H] [InnerProductSpace ℝ E]
  [CompleteSpace B] [CompleteSpace H] [CompleteSpace E]

theorem innerIsometricRestriction_selfAdjoint
    (i : H →ₗᵢ[ℝ] E) (A : H →L[ℝ] H) (A0 : E →L[ℝ] E)
    (hA : ∀ F, i (A F) = A0 (i F)) (hA0 : IsSelfAdjoint A0) :
    IsSelfAdjoint A := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro F K
  have h := hA0.isSymmetric (i F) (i K)
  simp only [ContinuousLinearMap.coe_coe] at h ⊢
  rw [← hA F, ← hA K, i.inner_map_map, i.inner_map_map] at h
  exact h

/-- The adjoint of the actual Poisson field is the ambient adjoint
evaluated on the isometric inclusion of the same source. -/
theorem innerIsometricPoisson_adjoint_apply
    (i : H →ₗᵢ[ℝ] E) (P : B →L[ℝ] H) (P0 : B →L[ℝ] E)
    (hP : ∀ ξ, i (P ξ) = P0 ξ) (F : H) :
    P.adjoint F = P0.adjoint (i F) := by
  apply ext_inner_right ℝ
  intro ξ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    ← hP ξ, i.inner_map_map]

/-- The physical Schur expression is the restriction of that same
ambient expression, including its actual Poisson adjoint. -/
theorem innerIsometricSchur_apply
    (i : H →ₗᵢ[ℝ] E) (D : H →L[ℝ] H) (D0 : E →L[ℝ] E)
    (P : B →L[ℝ] H) (P0 : B →L[ℝ] E) (K : B →L[ℝ] B)
    (hD : ∀ F, i (D F) = D0 (i F))
    (hP : ∀ ξ, i (P ξ) = P0 ξ) (F : H) :
    i (D F + P (K (P.adjoint F))) =
      D0 (i F) + P0 (K (P0.adjoint (i F))) := by
  rw [map_add, hD, hP, innerIsometricPoisson_adjoint_apply i P P0 hP F]

end HilbertTransfer

end ContinuousFlexibility.Radial
