module

public import ContinuousFlexibility.Radial.InnerHardyPoissonEnergy

/-!
# Full-reference Poisson control with Hardy gap terms

The complete positive gap matrices remain in the common reference
matrix.  Orthogonal piece projections and the exact cut incidence
absorb the Hardy endpoint costs without a factor for the number of gaps.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "ambient" => InnerBorderL2 (radialHilbertMeasure D)
local notation "sets" => (fun p : Fin (n + 1) => Ioo (G.left p) (G.right p))
local notation "projection" => innerBorderPieceProjection (radialHilbertMeasure D) sets central

theorem weighted_poisson_bound_hardy (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hj : 0 < j)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2) (hκ : ∀ i, 0 < C.kappa i)
    (hmodelκ : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = .inl M → ∀ i, 0 < M.kappa i)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = .inl M → ∀ i,
        ‖(innerChainScalarRestriction n p w 1 i * Real.sqrt (M.kappa i))⁻¹ •
          innerBorderFieldMap (radialHilbertMeasure D)
            (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (M.column i)‖ ≤ K / j)
    (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p), C.piece p = .inr Q →
      ∃ c : ℝ, 0 < c ∧ EqOn W (fun _ => c) (Ioo (G.left p) (G.right p)) ∧
        (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p w 1 1 = c))
    (hendpoints : ∀ (i : Fin n) (Q : InnerRadialGapChart D G j central i.succ),
      C.piece i.succ = .inr Q → D.w (G.left i.succ) / G.left i.succ ≤ L * C.kappa i) :
    ‖(innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) ∘L
      C.ambientPoisson hDw ∘L innerBoundaryDiagonal (fun i => (w i)⁻¹)) ∘L
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt C.referenceMatrix)‖ ≤
      Real.sqrt (max ((2 * K / j) ^ 2) 48 + 24 * L) := by
  let d : ℝ := max ((2 * K / j) ^ 2) 48
  let cost : ℝ := d + 24 * L
  have hd : 0 ≤ d := (sq_nonneg _).trans (le_max_left _ _)
  have hcost : 0 ≤ cost := add_nonneg hd (mul_nonneg (by norm_num) hL)
  let MW := innerBorderFieldMap (radialHilbertMeasure D)
    (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
  let Ω := innerBoundaryDiagonal (fun i => (w i)⁻¹)
  let J := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (innerInterfaceInverseSqrt C.referenceMatrix)
  let A : Fin (n + 1) → B → ambient := fun p ξ =>
    projection p (MW ((C.piece p).poisson hDw.continuous (innerChainBoundaryCLM n p (Ω ξ))))
  let E : Fin (n + 1) → B → ℝ := fun p ξ =>
    ⟪innerChainBoundaryCLM n p ξ,
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C.piece p).referenceMatrix
        (innerChainBoundaryCLM n p ξ)⟫_ℝ
  have hlocal (p : Fin (n + 1)) (ξ : B) :
      ‖A p ξ‖ ^ 2 ≤ d * E p ξ +
        24 * C.hardyEndpointCoefficient p * (innerChainBoundaryCLM n p ξ 0) ^ 2 := by
    cases hp : C.piece p with
    | inl M =>
      have h := M.weighted_poisson_energy W hW CW hWC w hw (hmodelκ p M hp)
        hK (le_refl (2 * K)) hj (hmodels p M hp) ξ
      have he : 0 ≤ ⟪innerChainBoundaryCLM n p ξ,
          innerBoundaryDiagonal M.kappa (innerChainBoundaryCLM n p ξ)⟫_ℝ :=
        (innerMatrix_toEuclideanCLM_isPositive
          (Matrix.posSemidef_diagonal_iff.mpr
            (fun i => (hmodelκ p M hp i).le))).inner_nonneg_right _
      have hc := h.trans (mul_le_mul_of_nonneg_right
        (le_max_left ((2 * K / j) ^ 2) 48) he)
      simpa only [A, E, MW, Ω, hp, InnerRadialActualPiece.poisson,
        InnerRadialActualPiece.referenceMatrix, InnerRadialActualPiece.kappa,
        InnerRadialActualPiece.gapMatrix, add_zero, hardyEndpointCoefficient,
        mul_zero, zero_mul, innerBoundaryDiagonal, d] using hc
    | inr Q =>
      obtain ⟨c, hc, hconstant, hleft, hright⟩ := hgaps p Q hp
      have h := Q.weighted_poisson_energy_hardy hDw W hW CW hWC w hc hconstant
        hleft hright hjhalf ξ
      have he := Q.poisson_energy_nonneg hDw (innerChainBoundaryCLM n p ξ)
      have hc := h.trans (add_le_add
        (mul_le_mul_of_nonneg_right (le_max_right ((2 * K / j) ^ 2) 48) he) le_rfl)
      simpa only [A, E, MW, Ω, hp, InnerRadialActualPiece.poisson,
        InnerRadialActualPiece.referenceMatrix, InnerRadialActualPiece.kappa,
        InnerRadialActualPiece.gapMatrix, Matrix.diagonal_zero', zero_add,
        hardyEndpointCoefficient, d] using hc
  have hsum (ξ : B) : MW (C.ambientPoisson hDw (Ω ξ)) = ∑ p, A p ξ := by
    simp only [ambientPoisson, sum_apply, ContinuousLinearMap.comp_apply, map_sum, A]
    apply Finset.sum_congr rfl
    intro p _
    exact innerBorderPieceProjection_weight_commute (radialHilbertMeasure D) sets central
      (fun _ => measurableSet_Ioo) W hW CW hWC p _
  have horth (ξ : B) (p q : Fin (n + 1)) (hpq : p ≠ q) : ⟪A p ξ, A q ξ⟫_ℝ = 0 :=
    innerBorderPieceProjections_orthogonal (radialHilbertMeasure D) sets central
      (fun _ => measurableSet_Ioo) (innerRadialChainPieces_disjoint D G) _ _ hpq
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg cost)
  intro ξ
  simp only [ContinuousLinearMap.comp_apply]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg cost) (norm_nonneg ξ))).mp
  have henergy := innerMatrix_inverseSqrt_energy C.referenceMatrix
    (C.referenceMatrix_posDef hDw hκ) ξ
  have hend := C.hardy_endpoint_energy_le hDw hL hκ hendpoints (J ξ)
  calc
    ‖MW (C.ambientPoisson hDw (Ω (J ξ)))‖ ^ 2 = ∑ p, ‖A p (J ξ)‖ ^ 2 := by
      rw [hsum]
      exact inner_orthogonal_sum_norm_sq _ (horth (J ξ))
    _ ≤ ∑ p, (d * E p (J ξ) +
        24 * C.hardyEndpointCoefficient p * (innerChainBoundaryCLM n p (J ξ) 0) ^ 2) :=
      Finset.sum_le_sum (fun p _ => hlocal p (J ξ))
    _ = d * ∑ p, E p (J ξ) + 24 * ∑ p,
        C.hardyEndpointCoefficient p * (innerChainBoundaryCLM n p (J ξ) 0) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    _ ≤ d * ⟪J ξ, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.referenceMatrix (J ξ)⟫_ℝ +
        24 * (L * ⟪J ξ,
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.referenceMatrix (J ξ)⟫_ℝ) := by
      dsimp only [E]
      rw [← C.reference_energy]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hend (by norm_num))
    _ = (Real.sqrt cost * ‖ξ‖) ^ 2 := by
      rw [henergy, mul_pow, Real.sq_sqrt hcost]
      dsimp only [cost]
      ring

end InnerRadialActualChain

end ContinuousFlexibility.Radial
