import ContinuousFlexibility.Radial.InnerRadialPoissonEnergy
import ContinuousFlexibility.Radial.InnerSupportedWeights

/-!
# Weighted Poisson control for the same actual finite chain

The model input is a bound on the genuine normalized unit columns.
The gap input consists of its actual positive slope and a physical
weight constant on that gap and its active cuts. These imply local
quadratic energy estimates. Orthogonality and the exact full reference
normalization then give the j-inverse bound for the same assembled
Poisson map, independently of the number of pieces.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

private theorem innerPoissonCoefficient_sq_le {a b j e : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hj : 0 < j) (he : 0 ≤ e) :
    (a / j) ^ 2 * e ≤ (b / j) ^ 2 * e :=
  mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (div_nonneg ha hj.le) (div_nonneg (ha.trans hab) hj.le)).mpr
      (div_le_div_of_nonneg_right hab hj.le)) he

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  {piece : Fin (n + 1)} (A : InnerRadialModelChart D G bordered j central column piece)

theorem weighted_poisson_energy
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hκ : ∀ i, 0 < A.kappa i)
    {K L : ℝ} (hK : 0 ≤ K) (hKL : 2 * K ≤ L) (hj : 0 < j)
    (hcolumns : ∀ i,
      ‖(innerChainScalarRestriction n piece w 1 i * Real.sqrt (A.kappa i))⁻¹ •
        innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (A.column i)‖ ≤ K / j)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun p => Ioo (G.left p) (G.right p)) central piece
        (innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
          (A.poisson (innerChainBoundaryCLM n piece
            (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ))))‖ ^ 2 ≤
      (L / j) ^ 2 * ⟪innerChainBoundaryCLM n piece ξ,
        innerBoundaryDiagonal A.kappa (innerChainBoundaryCLM n piece ξ)⟫_ℝ := by
  let MW := innerBorderFieldMap (radialHilbertMeasure D)
    (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
  let z := innerChainBoundaryCLM n piece ξ
  have hlocal := innerTwoColumnMap_weighted_energy A.column MW
    (innerChainScalarRestriction n piece w 1) A.kappa
    (innerChainScalarRestriction_pos n piece w hw (by norm_num)) hκ hK hj hcolumns z
  have hraw : ‖MW (A.poisson (innerChainBoundaryCLM n piece
      (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ)))‖ ^ 2 ≤
        ((2 * K) / j) ^ 2 * ⟪z, innerBoundaryDiagonal A.kappa z⟫_ℝ := by
    simpa only [InnerRadialModelChart.poisson, innerChainBoundaryCLM_inverse_diagonal] using hlocal
  have henergy : 0 ≤ ⟪z, innerBoundaryDiagonal A.kappa z⟫_ℝ :=
    (innerMatrix_toEuclideanCLM_isPositive
      (Matrix.posSemidef_diagonal_iff.mpr (fun i => (hκ i).le))).inner_nonneg_right z
  have hproj := innerBorderPieceProjection_contract (radialHilbertMeasure D)
    (fun p => Ioo (G.left p) (G.right p)) central (fun _ => measurableSet_Ioo) piece
      (MW (A.poisson (innerChainBoundaryCLM n piece
        (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ))))
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hproj).trans
    (hraw.trans (innerPoissonCoefficient_sq_le (mul_nonneg (by norm_num) hK) hKL hj henergy))

end InnerRadialModelChart

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)} (A : InnerRadialGapChart D G j central piece)

theorem weighted_poisson_energy (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) {s L c : ℝ} (hs : 0 < s) (hslope : s ≤ A.slope)
    (hL : Real.sqrt (12 / s) ≤ L) (hc : 0 < c)
    (hconstant : EqOn W (fun _ => c) (Ioo (G.left piece) (G.right piece)))
    (hleft : 0 < piece.val → innerChainScalarRestriction n piece w 1 0 = c)
    (hright : piece.val < n → innerChainScalarRestriction n piece w 1 1 = c)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖innerBorderPieceProjection (radialHilbertMeasure D)
        (fun p => Ioo (G.left p) (G.right p)) central piece
        (innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
          (A.poisson hDw.continuous (innerChainBoundaryCLM n piece
            (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ))))‖ ^ 2 ≤
      (L / j) ^ 2 * ⟪innerChainBoundaryCLM n piece ξ,
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A.fluxMatrix
          (innerChainBoundaryCLM n piece ξ)⟫_ℝ := by
  rw [innerChainBoundary_inverse_weight_constant n piece w c hleft hright,
    A.poisson_weight_cancel hDw.continuous W hW CW hWC c hc.ne' hconstant]
  have hproj := innerBorderPieceProjection_contract (radialHilbertMeasure D)
    (fun p => Ioo (G.left p) (G.right p)) central (fun _ => measurableSet_Ioo) piece
      (A.poisson hDw.continuous (innerChainBoundaryCLM n piece ξ))
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hproj).trans
    ((A.poisson_norm_sq_le hDw hs hslope _).trans
      (innerPoissonCoefficient_sq_le (Real.sqrt_nonneg _) hL A.frequency_pos
        (A.poisson_energy_nonneg hDw _)))

end InnerRadialGapChart

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "ambient" => InnerBorderL2 (radialHilbertMeasure D)
local notation "sets" => (fun p : Fin (n + 1) => Ioo (G.left p) (G.right p))
local notation "projection" => innerBorderPieceProjection (radialHilbertMeasure D) sets central

theorem reference_energy (ξ : B) :
    ⟪ξ, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.referenceMatrix ξ⟫_ℝ =
      ∑ p, ⟪innerChainBoundaryCLM n p ξ,
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C.piece p).referenceMatrix
          (innerChainBoundaryCLM n p ξ)⟫_ℝ := by
  rw [referenceMatrix, innerChainErrorMatrix_toEuclideanCLM]
  have h := innerInterfaceBlockSum_inner (innerChainBoundaryCLM n)
    (fun p => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C.piece p).referenceMatrix) ξ ξ
  simpa only [real_inner_comm] using h

/-- Quadratic local estimates combine using the actual orthogonal
piece projections and the exact full reference energy. -/
theorem weighted_poisson_of_local_energy (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) {L : ℝ} (hL : 0 ≤ L) (hj : 0 < j)
    (hκ : ∀ i, 0 < C.kappa i)
    (hlocal : ∀ p ξ,
      ‖projection p (innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
        ((C.piece p).poisson hDw.continuous (innerChainBoundaryCLM n p
          (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ))))‖ ^ 2 ≤
      (L / j) ^ 2 * ⟪innerChainBoundaryCLM n p ξ,
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C.piece p).referenceMatrix
          (innerChainBoundaryCLM n p ξ)⟫_ℝ) :
    ‖(innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) ∘L
      C.ambientPoisson hDw ∘L innerBoundaryDiagonal (fun i => (w i)⁻¹)) ∘L
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt C.referenceMatrix)‖ ≤ L / j := by
  let MW := innerBorderFieldMap (radialHilbertMeasure D)
    (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
  let Ω := innerBoundaryDiagonal (fun i => (w i)⁻¹)
  let J := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (innerInterfaceInverseSqrt C.referenceMatrix)
  let A : Fin (n + 1) → B → ambient := fun p ξ =>
    projection p (MW ((C.piece p).poisson hDw.continuous (innerChainBoundaryCLM n p (Ω ξ))))
  have hsum (ξ : B) : MW (C.ambientPoisson hDw (Ω ξ)) = ∑ p, A p ξ := by
    simp only [ambientPoisson, sum_apply, ContinuousLinearMap.comp_apply, map_sum, A]
    apply Finset.sum_congr rfl
    intro p _
    exact innerBorderPieceProjection_weight_commute (radialHilbertMeasure D) sets central
      (fun _ => measurableSet_Ioo) W hW CW hWC p _
  have horth (ξ : B) (p q : Fin (n + 1)) (hpq : p ≠ q) : ⟪A p ξ, A q ξ⟫_ℝ = 0 :=
    innerBorderPieceProjections_orthogonal (radialHilbertMeasure D) sets central
      (fun _ => measurableSet_Ioo) (innerRadialChainPieces_disjoint D G) _ _ hpq
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hL hj.le)
  intro ξ
  simp only [ContinuousLinearMap.comp_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg hL hj.le) (norm_nonneg ξ))).mp
  have henergy := innerMatrix_inverseSqrt_energy C.referenceMatrix
    (C.referenceMatrix_posDef hDw hκ) ξ
  calc
    ‖MW (C.ambientPoisson hDw (Ω (J ξ)))‖ ^ 2 = ∑ p, ‖A p (J ξ)‖ ^ 2 := by
      rw [hsum]
      exact inner_orthogonal_sum_norm_sq _ (horth (J ξ))
    _ ≤ (L / j) ^ 2 * ∑ p, ⟪innerChainBoundaryCLM n p (J ξ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C.piece p).referenceMatrix
          (innerChainBoundaryCLM n p (J ξ))⟫_ℝ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun p _ => hlocal p (J ξ))
    _ = (L / j) ^ 2 * ⟪J ξ,
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.referenceMatrix (J ξ)⟫_ℝ := by
      rw [C.reference_energy]
    _ = ((L / j) * ‖ξ‖) ^ 2 := by rw [henergy, mul_pow]

/-- The actual model-column estimates and gap geometry prove the full
weighted Poisson estimate for this very same dictionary and reference.
The theorem applies unchanged to either reciprocal weight sign. -/
theorem weighted_poisson_bound (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hj : 0 < j)
    (hκ : ∀ i, 0 < C.kappa i)
    (hmodelκ : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → ∀ i, 0 < M.kappa i)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = Sum.inl M → ∀ i,
        ‖(innerChainScalarRestriction n p w 1 i * Real.sqrt (M.kappa i))⁻¹ •
          innerBorderFieldMap (radialHilbertMeasure D)
            (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (M.column i)‖ ≤ K / j)
    (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p), C.piece p = Sum.inr Q →
      s ≤ Q.slope ∧ ∃ c : ℝ, 0 < c ∧
        EqOn W (fun _ => c) (Ioo (G.left p) (G.right p)) ∧
        (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p w 1 1 = c)) :
    ‖(innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) ∘L
      C.ambientPoisson hDw ∘L innerBoundaryDiagonal (fun i => (w i)⁻¹)) ∘L
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt C.referenceMatrix)‖ ≤
      max (2 * K) (Real.sqrt (12 / s)) / j := by
  apply C.weighted_poisson_of_local_energy hDw W hW CW hWC w
    ((mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK).trans (le_max_left _ _)) hj hκ
  intro p ξ
  cases hp : C.piece p with
  | inl M =>
    have h := M.weighted_poisson_energy W hW CW hWC w hw (hmodelκ p M hp) hK
      (le_max_left (2 * K) (Real.sqrt (12 / s))) hj (hmodels p M hp) ξ
    simpa only [hp, InnerRadialActualPiece.poisson, InnerRadialActualPiece.referenceMatrix,
      InnerRadialActualPiece.kappa, InnerRadialActualPiece.gapMatrix, add_zero,
      innerBoundaryDiagonal] using h
  | inr Q =>
    obtain ⟨hslope, c, hc, hconstant, hleft, hright⟩ := hgaps p Q hp
    have h := Q.weighted_poisson_energy hDw W hW CW hWC w hs hslope
      (le_max_right (2 * K) (Real.sqrt (12 / s))) hc hconstant hleft hright ξ
    simpa only [hp, InnerRadialActualPiece.poisson, InnerRadialActualPiece.referenceMatrix,
      InnerRadialActualPiece.kappa, InnerRadialActualPiece.gapMatrix,
      Matrix.diagonal_zero', zero_add] using h

/-- Restricting to the genuine supported source costs no constant.
Thus the previous actual ambient estimate applies to the very Poisson
operator whose adjoint occurs in the physical inverse formula. -/
theorem weighted_poisson_norm_le_ambient (hDw : ContDiff ℝ ∞ D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (w : Fin n → ℝ) :
    ‖(innerSupportedWeightMultiplier (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G)
        bordered W hW CW hWC ∘L C.poisson hDw ∘L
        innerBoundaryDiagonal (fun i => (w i)⁻¹)) ∘L
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
            (innerInterfaceInverseSqrt C.referenceMatrix)‖ ≤
      ‖(innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) ∘L
        C.ambientPoisson hDw ∘L innerBoundaryDiagonal (fun i => (w i)⁻¹)) ∘L
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
            (innerInterfaceInverseSqrt C.referenceMatrix)‖ := by
  apply innerIsometricOperator_norm_le (LinearIsometry.id ℝ B)
    (innerRadialPhysicalInclusion D G bordered)
  intro ξ
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.id_apply,
    innerRadialPhysicalInclusion_apply, innerSupportedWeightMultiplier_apply,
    C.poisson_ambient]

end InnerRadialActualChain

end ContinuousFlexibility.Radial
