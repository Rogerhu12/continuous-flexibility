import ContinuousFlexibility.Radial.InnerRadialActualAssembly
import ContinuousFlexibility.Radial.InnerGapAssemblyData

/-!
# The exact full reference matrix of the actual chain

Each internal cut receives the endpoint diagonal contributions of its
two incident pieces. Positive gaps contribute zero to this diagonal;
their entire two-by-two DtN blocks, including off-diagonal entries,
remain in the reference. This is the same S0 used by the weak flux and
the matrix estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators MatrixOrder

def innerChainAggregateKappa (n : ℕ) (κ : Fin (n + 1) → Fin 2 → ℝ) (i : Fin n) : ℝ :=
  κ i.castSucc 1 + κ i.succ 0

theorem innerChainBoundary_diagonal_bilinear (n : ℕ)
    (κ : Fin (n + 1) → Fin 2 → ℝ) (ξ η : EuclideanSpace ℝ (Fin n)) :
    (∑ p, κ p 0 * innerChainBoundaryRestriction n p ξ 0 *
        innerChainBoundaryRestriction n p η 0 +
      κ p 1 * innerChainBoundaryRestriction n p ξ 1 *
        innerChainBoundaryRestriction n p η 1) =
      ∑ i, innerChainAggregateKappa n κ i * ξ i * η i := by
  have hleft :
      (∑ p, κ p 0 * innerChainBoundaryRestriction n p ξ 0 *
        innerChainBoundaryRestriction n p η 0) = ∑ i : Fin n, κ i.succ 0 * ξ i * η i := by
    rw [Fin.sum_univ_succ]
    simp only [(innerChainBoundaryRestriction_outer n ξ).1,
      (innerChainBoundaryRestriction_outer n η).1, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [(innerChainBoundaryRestriction_match n i ξ).2,
      (innerChainBoundaryRestriction_match n i η).2]
  have hright :
      (∑ p, κ p 1 * innerChainBoundaryRestriction n p ξ 1 *
        innerChainBoundaryRestriction n p η 1) = ∑ i : Fin n, κ i.castSucc 1 * ξ i * η i := by
    rw [Fin.sum_univ_castSucc]
    simp only [(innerChainBoundaryRestriction_outer n ξ).2,
      (innerChainBoundaryRestriction_outer n η).2, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [(innerChainBoundaryRestriction_match n i ξ).1,
      (innerChainBoundaryRestriction_match n i η).1]
  rw [Finset.sum_add_distrib, hleft, hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold innerChainAggregateKappa
  ring

theorem innerChainDiagonal_blockSum (n : ℕ)
    (κ : Fin (n + 1) → Fin 2 → ℝ) :
    innerInterfaceBlockSum (innerChainBoundaryCLM n)
      (fun p => innerBoundaryDiagonal (κ p)) =
        innerBoundaryDiagonal (innerChainAggregateKappa n κ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℝ
  intro η
  rw [innerInterfaceBlockSum_inner]
  have h := innerChainBoundary_diagonal_bilinear n κ ξ η
  simpa only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    innerBoundaryDiagonal_apply, innerChainBoundaryCLM_apply,
    mul_comm, mul_left_comm, mul_assoc] using h

theorem innerChainErrorMatrix_add (n : ℕ)
    (A B : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ) :
    innerChainErrorMatrix n (fun p => A p + B p) =
      innerChainErrorMatrix n A + innerChainErrorMatrix n B := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  simp only [map_add, innerChainErrorMatrix_toEuclideanCLM, innerInterfaceBlockSum,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, Finset.sum_add_distrib]

theorem innerChainErrorMatrix_diagonal (n : ℕ)
    (κ : Fin (n + 1) → Fin 2 → ℝ) :
    innerChainErrorMatrix n (fun p => Matrix.diagonal (κ p)) =
      Matrix.diagonal (innerChainAggregateKappa n κ) := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  rw [innerChainErrorMatrix_toEuclideanCLM]
  exact innerChainDiagonal_blockSum n κ

theorem innerChainErrorMatrix_posSemidef (n : ℕ)
    (A : Fin (n + 1) → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ p, (A p).PosSemidef) : (innerChainErrorMatrix n A).PosSemidef := by
  have h : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (innerChainErrorMatrix n A)).IsPositive := by
    rw [innerChainErrorMatrix_toEuclideanCLM]
    apply ContinuousLinearMap.isPositive_sum
    intro p _
    exact (innerMatrix_toEuclideanCLM_isPositive (hA p)).adjoint_conj
      (innerChainBoundaryCLM n p)
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  simpa only [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr h

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

def kappa : Fin n → ℝ := innerChainAggregateKappa n (fun p => (C.piece p).kappa)

def gapMatrix : Matrix (Fin n) (Fin n) ℝ :=
  innerChainErrorMatrix n (fun p => (C.piece p).gapMatrix)

/-- Exact endpoint incidence, useful for identifying each retained
model endpoint with the common global cut normalization. -/
theorem kappa_apply (i : Fin n) :
    C.kappa i = (C.piece i.castSucc).kappa 1 + (C.piece i.succ).kappa 0 := rfl

theorem kappa_eq_right (i : Fin n) (hgap : (C.piece i.succ).kappa 0 = 0) :
    C.kappa i = (C.piece i.castSucc).kappa 1 := by rw [C.kappa_apply, hgap, add_zero]

theorem kappa_eq_left (i : Fin n) (hgap : (C.piece i.castSucc).kappa 1 = 0) :
    C.kappa i = (C.piece i.succ).kappa 0 := by rw [C.kappa_apply, hgap, zero_add]

/-- The reference keeps the entire gap matrix, not only its diagonal. -/
theorem referenceMatrix_eq :
    C.referenceMatrix = Matrix.diagonal C.kappa + C.gapMatrix := by
  simp only [referenceMatrix, InnerRadialActualPiece.referenceMatrix,
    innerChainErrorMatrix_add, innerChainErrorMatrix_diagonal, kappa, gapMatrix]

theorem gapMatrix_posSemidef (hw : ContDiff ℝ ∞ D.w) : C.gapMatrix.PosSemidef := by
  apply innerChainErrorMatrix_posSemidef
  intro p
  cases hp : C.piece p with
  | inl M =>
    simp only [hp, InnerRadialActualPiece.gapMatrix]
    exact Matrix.PosSemidef.zero
  | inr Q =>
    simpa only [hp, InnerRadialActualPiece.gapMatrix, InnerRadialGapChart.fluxMatrix] using
      innerGapFluxMatrix_posSemidef (G.left_lt_right p).le (G.left_pos p) hw
        Q.columns Q.columns_smooth Q.columns_boundary Q.columns_homogeneous
        (G.weight_pos p) (fun r hr => Q.slope_pos.le.trans (Q.slope_lower r hr))

theorem referenceMatrix_posDef (hw : ContDiff ℝ ∞ D.w)
    (hκ : ∀ i, 0 < C.kappa i) : C.referenceMatrix.PosDef := by
  rw [C.referenceMatrix_eq]
  exact (Matrix.posDef_diagonal_iff.mpr hκ).add_posSemidef (C.gapMatrix_posSemidef hw)

theorem diagonal_le_referenceMatrix (hw : ContDiff ℝ ∞ D.w) :
    Matrix.diagonal C.kappa ≤ C.referenceMatrix := by
  rw [C.referenceMatrix_eq]
  exact le_add_of_nonneg_right (C.gapMatrix_posSemidef hw).nonneg

end InnerRadialActualChain

end ContinuousFlexibility.Radial
