import ContinuousFlexibility.Radial.InnerRadialActualInverse
import ContinuousFlexibility.Radial.InnerRadialPoissonEnergy

/-!
# The actual weighted interface from local model errors

The full gap blocks commute with the cut weight because its two active
endpoint values agree. Exterior zero traces need no extra weight value.
The retained model diagonals commute automatically. Thus the same full
reference matrix, including every gap off-diagonal, commutes with the
actual diagonal weight.

At each internal cut only one incident piece contributes a model
diagonal. This identifies the local and global energy normalizations.
The two weighted local errors then give both strict one-half estimates
for the same assembled interface; global smallness is a conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators MatrixOrder Matrix.Norms.L2Operator

/-- Every nonzero block with a common active cut weight commutes after
extension by the actual incidence maps. The local block is arbitrary. -/
theorem innerChainBlockSum_commute_of_constant_weights (n : ℕ) (w : Fin n → ℝ)
    (K : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hK : ∀ p, K p = 0 ∨ ∃ c : ℝ,
      (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
      (p.val < n → innerChainScalarRestriction n p w 1 1 = c)) :
    Commute (innerBoundaryDiagonal w)
      (innerInterfaceBlockSum (innerChainBoundaryCLM n) K) := by
  apply (commute_iff_eq (innerBoundaryDiagonal w)
    (innerInterfaceBlockSum (innerChainBoundaryCLM n) K)).mpr
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℝ
  intro η
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  have hsym :
      ⟪innerBoundaryDiagonal w (innerInterfaceBlockSum (innerChainBoundaryCLM n) K ξ), η⟫_ℝ =
        ⟪innerInterfaceBlockSum (innerChainBoundaryCLM n) K ξ,
          innerBoundaryDiagonal w η⟫_ℝ := by
    simpa only [ContinuousLinearMap.coe_coe] using
      (innerBoundaryDiagonal_selfAdjoint w).isSymmetric
        (innerInterfaceBlockSum (innerChainBoundaryCLM n) K ξ) η
  rw [hsym, innerInterfaceBlockSum_inner, innerInterfaceBlockSum_inner]
  apply Finset.sum_congr rfl
  intro p _
  rcases hK p with hzero | ⟨c, hleft, hright⟩
  · simp only [hzero, ContinuousLinearMap.zero_apply, inner_zero_left]
  · rw [innerChainBoundary_weight_constant n p w c hleft hright η,
      innerChainBoundary_weight_constant n p w c hleft hright ξ,
      map_smul, real_inner_smul_left, real_inner_smul_right]

/-- With separated retained models, the aggregate cut coefficient is
exactly the coefficient of the model incident to that cut. -/
theorem innerChainAggregateKappa_restriction_of_separated (n : ℕ)
    (κ : Fin (n + 1) → Fin 2 → ℝ)
    (hsep : ∀ i : Fin n, κ i.castSucc 1 = 0 ∨ κ i.succ 0 = 0)
    (p : Fin (n + 1)) (hleft : 0 < p.val) (hright : p.val < n)
    (hκ : ∀ i, 0 < κ p i) :
    innerChainScalarRestriction n p (innerChainAggregateKappa n κ) 1 = κ p := by
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · let k : Fin n := ⟨p.val - 1, by omega⟩
    have hk : k.succ = p := by
      apply Fin.ext
      simp only [Fin.val_succ, k]
      omega
    have hz : κ k.castSucc 1 = 0 := by
      rcases hsep k with hzero | hzero
      · exact hzero
      · exact False.elim ((hκ 0).ne' (by simpa only [hk] using hzero))
    have he : innerChainAggregateKappa n κ k = κ p 0 := by
      rw [innerChainAggregateKappa, hz, hk, zero_add]
    simpa only [innerChainScalarRestriction, ite_true, dif_pos hleft, k] using he
  · let k : Fin n := ⟨p.val, hright⟩
    have hk : k.castSucc = p := by
      apply Fin.ext
      simp only [Fin.val_castSucc, k]
    have hz : κ k.succ 0 = 0 := by
      rcases hsep k with hzero | hzero
      · exact False.elim ((hκ 1).ne' (by simpa only [hk] using hzero))
      · exact hzero
    have he : innerChainAggregateKappa n κ k = κ p 1 := by
      rw [innerChainAggregateKappa, hz, hk, add_zero]
    simpa only [innerChainScalarRestriction, show (1 : Fin 2) ≠ 0 by decide,
      ite_false, dif_pos hright, k] using he

@[simp] theorem innerTwoCutWeightedError_zero (κ w : Fin 2 → ℝ) (sign : Bool) :
    innerTwoCutWeightedError κ w 0 sign = 0 := by
  ext i k
  simp only [innerTwoCutWeightedError, Matrix.zero_apply, zero_div, mul_zero]

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- Only the actual gap cut-weight agreement is used; all model
diagonals and all full gap blocks remain in the reference matrix. -/
theorem referenceMatrix_commute (w : Fin n → ℝ)
    (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p), C.piece p = .inr Q →
      ∃ c : ℝ,
        (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p w 1 1 = c)) :
    Commute (Matrix.diagonal w) C.referenceMatrix := by
  rw [C.referenceMatrix_eq]
  apply (Matrix.commute_diagonal w C.kappa).add_right
  apply Commute.of_map (f := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
    (EquivLike.injective (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)))
  rw [gapMatrix, innerChainErrorMatrix_toEuclideanCLM]
  apply innerChainBlockSum_commute_of_constant_weights
  intro p
  cases hp : C.piece p with
  | inl M =>
    left
    simp only [hp, InnerRadialActualPiece.gapMatrix, map_zero]
  | inr Q =>
    exact Or.inr (hgaps p Q hp)

theorem model_kappa_restriction
    (hsep : ∀ i : Fin n,
      (C.piece i.castSucc).kappa 1 = 0 ∨ (C.piece i.succ).kappa 0 = 0)
    (p : Fin (n + 1)) (M : InnerRadialModelChart D G bordered j central column p)
    (hp : C.piece p = .inl M) (hleft : 0 < p.val) (hright : p.val < n)
    (hκ : ∀ i, 0 < M.kappa i) :
    innerChainScalarRestriction n p C.kappa 1 = M.kappa := by
  have hlocal : ∀ i, 0 < (C.piece p).kappa i := by
    simpa only [hp, InnerRadialActualPiece.kappa] using hκ
  have h := innerChainAggregateKappa_restriction_of_separated n
    (fun q => (C.piece q).kappa) hsep p hleft hright hlocal
  simpa only [kappa, hp, InnerRadialActualPiece.kappa] using h

/-- The two signs use the same actual model errors. Gap errors are
zero; the gap reference is unchanged. -/
theorem normalized_error_both (hw : ContDiff ℝ ∞ D.w)
    (hκ : ∀ i, 0 < C.kappa i) (w : Fin n → ℝ) (hwpos : ∀ i, 0 < w i)
    (hsep : ∀ i : Fin n,
      (C.piece i.castSucc).kappa 1 = 0 ∨ (C.piece i.succ).kappa 0 = 0)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = .inl M → 0 < p.val ∧ p.val < n ∧ ∀ i, 0 < M.kappa i)
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (herror : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = .inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa (innerChainScalarRestriction n p w 1)
          M.errorMatrix sign‖ ≤ η) (sign : Bool) :
    ‖innerInterfaceWeightedError C.referenceMatrix
      (innerInterfaceWeight (Matrix.diagonal w) sign) C.errorMatrix‖ < 1 / 2 := by
  apply innerChainErrorMatrix_normalized_both n C.referenceMatrix C.kappa w
    (C.referenceMatrix_posDef hw hκ) hκ hwpos (C.diagonal_le_referenceMatrix hw)
    (fun p => (C.piece p).errorMatrix) hη hηsmall
  intro p sign
  cases hp : C.piece p with
  | inl M =>
    rcases hmodels p M hp with ⟨hleft, hright, hlocalκ⟩
    rw [InnerRadialActualPiece.errorMatrix,
      C.model_kappa_restriction hsep p M hp hleft hright hlocalκ]
    exact herror p M hp sign
  | inr Q =>
    simpa only [hp, InnerRadialActualPiece.errorMatrix,
      innerTwoCutWeightedError_zero, norm_zero] using hη

/-- Actual local two-cut bounds and gap weight geometry imply
invertibility of the same full physical flux matrix. -/
theorem fluxMatrix_isUnit_of_local_errors (hw : ContDiff ℝ ∞ D.w)
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
          M.errorMatrix sign‖ ≤ η) :
    IsUnit C.fluxMatrix :=
  C.fluxMatrix_isUnit hw hκ (Matrix.diagonal w) (Matrix.posDef_diagonal_iff.mpr hwpos)
    (C.referenceMatrix_commute w hgaps)
    (C.normalized_error_both hw hκ w hwpos hsep hmodels hη hηsmall herror)

end InnerRadialActualChain

end ContinuousFlexibility.Radial
