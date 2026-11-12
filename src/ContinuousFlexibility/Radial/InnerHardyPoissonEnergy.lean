import ContinuousFlexibility.Radial.InnerRadialWeightedPoisson
import ContinuousFlexibility.Radial.InnerRadialGapHardy

/-!
# Hardy energy on actual gap columns and their common cut diagonal

Every gap keeps its full Dirichlet-to-Neumann matrix.  The extra left
endpoint term is charged exactly once to the adjacent internal cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)} (A : InnerRadialGapChart D G j central piece)

theorem weighted_poisson_energy_hardy (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    (hconstant : EqOn W (fun _ => c) (Ioo (G.left piece) (G.right piece)))
    (hleft : 0 < piece.val → innerChainScalarRestriction n piece w 1 0 = c)
    (hright : piece.val < n → innerChainScalarRestriction n piece w 1 1 = c)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun p => Ioo (G.left p) (G.right p)) central piece
        (innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
          (A.poisson hDw.continuous (innerChainBoundaryCLM n piece
            (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ))))‖ ^ 2 ≤
      48 * ⟪innerChainBoundaryCLM n piece ξ,
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A.fluxMatrix
          (innerChainBoundaryCLM n piece ξ)⟫_ℝ +
        24 * (D.w (G.left piece) / G.left piece) *
          (innerChainBoundaryCLM n piece ξ 0) ^ 2 := by
  rw [innerChainBoundary_inverse_weight_constant n piece w c hleft hright,
    A.poisson_weight_cancel hDw.continuous W hW CW hWC c hc.ne' hconstant]
  have hproj := innerBorderPieceProjection_contract (radialHilbertMeasure D)
    (fun p => Ioo (G.left p) (G.right p)) central (fun _ => measurableSet_Ioo) piece
      (A.poisson hDw.continuous (innerChainBoundaryCLM n piece ξ))
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hproj).trans
    (A.poisson_norm_sq_hardy hDw hjhalf _)

end InnerRadialGapChart

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (A : InnerRadialActualChain D G bordered j central column)

def hardyEndpointCoefficient (p : Fin (n + 1)) : ℝ :=
  match A.piece p with
  | .inl _ => 0
  | .inr _ => D.w (G.left p) / G.left p

theorem hardy_endpoint_energy_le (hw : ContDiff ℝ ∞ D.w) {L : ℝ}
    (hL : 0 ≤ L) (hκ : ∀ i, 0 < A.kappa i)
    (hendpoints : ∀ (i : Fin n) (Q : InnerRadialGapChart D G j central i.succ),
      A.piece i.succ = .inr Q → D.w (G.left i.succ) / G.left i.succ ≤ L * A.kappa i)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    (∑ p, A.hardyEndpointCoefficient p * (innerChainBoundaryCLM n p ξ 0) ^ 2) ≤
      L * ⟪ξ, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A.referenceMatrix ξ⟫_ℝ := by
  have hleft0 : innerChainBoundaryCLM n 0 ξ 0 = 0 :=
    (innerChainBoundaryRestriction_outer n ξ).1
  have hleft (i : Fin n) : innerChainBoundaryCLM n i.succ ξ 0 = ξ i :=
    (innerChainBoundaryRestriction_match n i ξ).2
  have hs : (∑ p, A.hardyEndpointCoefficient p *
      (innerChainBoundaryCLM n p ξ 0) ^ 2) ≤ L * ∑ i, A.kappa i * (ξ i) ^ 2 := by
    rw [Fin.sum_univ_succ, hleft0, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hleft]
    have hc : A.hardyEndpointCoefficient i.succ ≤ L * A.kappa i := by
      cases hp : A.piece i.succ with
      | inl M => simpa only [hardyEndpointCoefficient, hp] using mul_nonneg hL (hκ i).le
      | inr Q => simpa only [hardyEndpointCoefficient, hp] using hendpoints i Q hp
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans_eq (mul_assoc _ _ _)
  have hdiag : ⟪ξ, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (Matrix.diagonal A.kappa) ξ⟫_ℝ = ∑ i, A.kappa i * (ξ i) ^ 2 := by
    change ⟪ξ, innerBoundaryDiagonal A.kappa ξ⟫_ℝ = _
    simp only [PiLp.inner_apply, innerBoundaryDiagonal_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgap : 0 ≤ ⟪ξ, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      A.gapMatrix ξ⟫_ℝ :=
    (innerMatrix_toEuclideanCLM_isPositive (A.gapMatrix_posSemidef hw)).inner_nonneg_right ξ
  apply hs.trans
  rw [← hdiag, A.referenceMatrix_eq, map_add, ContinuousLinearMap.add_apply, inner_add_right]
  nlinarith only [hL, hgap]

end InnerRadialActualChain

end ContinuousFlexibility.Radial
