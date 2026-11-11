import ContinuousFlexibility.Radial.InnerModelPoissonNormalization
import ContinuousFlexibility.Radial.InnerChainBoundaryHilbert
import ContinuousFlexibility.Radial.InnerProjectedInverseBound
import ContinuousFlexibility.Radial.InnerChainDiagonal

/-!
# Finite assembly of the actual model Poisson columns

Two endpoint columns define one linear Poisson map. Their physical
weights and cut energies are normalized before summing over pieces.
Orthogonality of the physical intervals and the exact chain incidence
identity give constants independent of the number of retained cells.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

section Columns

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A two-endpoint Poisson map made from the actual unit columns. -/
def innerTwoColumnMap (p : Fin 2 → H) : EuclideanSpace ℝ (Fin 2) →L[ℝ] H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => ∑ i, ξ i • p i
      map_add' := by
        intro ξ η
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c ξ
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.smul_sum, smul_smul] }

theorem innerTwoColumnMap_apply (p : Fin 2 → H) (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerTwoColumnMap p ξ = ∑ i, ξ i • p i := by
  simp only [innerTwoColumnMap, LinearMap.coe_toContinuousLinearMap']

/-- Only the fixed two-endpoint dimension enters this estimate. -/
theorem innerTwoColumnMap_norm_le (p : Fin 2 → H) {K : ℝ}
    (hK : 0 ≤ K) (hp : ∀ i, ‖p i‖ ≤ K) : ‖innerTwoColumnMap p‖ ≤ 2 * K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  have hterm (i : Fin 2) : ‖ξ i • p i‖ ≤ ‖ξ‖ * K := by
    rw [norm_smul]
    exact mul_le_mul (PiLp.norm_apply_le ξ i) (hp i) (norm_nonneg _) (norm_nonneg _)
  rw [innerTwoColumnMap_apply, Fin.sum_univ_two]
  calc
    _ ≤ ‖ξ 0 • p 0‖ + ‖ξ 1 • p 1‖ := norm_add_le _ _
    _ ≤ ‖ξ‖ * K + ‖ξ‖ * K := add_le_add (hterm 0) (hterm 1)
    _ = (2 * K) * ‖ξ‖ := by ring

/-- This identity retains the very same physical unit columns. The
cut height is included in kappa, and each column uses its own cut weight. -/
theorem innerTwoColumnMap_weighted_normalization
    (p : Fin 2 → H) (W : H →L[ℝ] H) (w κ : Fin 2 → ℝ)
    (hw : ∀ i, 0 < w i) (hκ : ∀ i, 0 < κ i) (ξ : EuclideanSpace ℝ (Fin 2)) :
    W (innerTwoColumnMap p (WithLp.toLp 2 (fun i => (w i)⁻¹ * ξ i))) =
      innerTwoColumnMap (fun i => (w i * Real.sqrt (κ i))⁻¹ • W (p i))
        (WithLp.toLp 2 (fun i => Real.sqrt (κ i) * ξ i)) := by
  simp only [innerTwoColumnMap_apply, map_sum, map_smul, PiLp.toLp_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  field_simp [(hw i).ne', (Real.sqrt_pos.mpr (hκ i)).ne']

end Columns

section OrthogonalBoundarySum

variable {ι B E H : Type*} [Fintype ι]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The incidence constant two and physical orthogonality control a
boundary-to-field sum. Neither the source nor the output is replaced
by a product norm depending on the number of pieces. -/
theorem norm_innerOrthogonalBoundarySum_le
    (R : ι → B →L[ℝ] E) (A : ι → B →L[ℝ] H) {K : ℝ}
    (hK : 0 ≤ K) (hR : ∀ ξ, (∑ p, ‖R p ξ‖ ^ 2) ≤ 2 * ‖ξ‖ ^ 2)
    (horth : ∀ ξ p q, p ≠ q → ⟪A p ξ, A q ξ⟫_ℝ = 0)
    (hlocal : ∀ p ξ, ‖A p ξ‖ ≤ K * ‖R p ξ‖) :
    ‖∑ p, A p‖ ≤ 2 * K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  have hsum : ‖∑ p, A p ξ‖ ^ 2 = ∑ p, ‖A p ξ‖ ^ 2 :=
    inner_orthogonal_sum_norm_sq _ (horth ξ)
  have hsq : ‖∑ p, A p ξ‖ ^ 2 ≤ 2 * K ^ 2 * ‖ξ‖ ^ 2 := by
    rw [hsum]
    calc
      _ ≤ ∑ p, K ^ 2 * ‖R p ξ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p _
        simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr (hlocal p ξ)
      _ = K ^ 2 * ∑ p, ‖R p ξ‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ K ^ 2 * (2 * ‖ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hR ξ) (sq_nonneg K)
      _ = _ := by ring
  have hlast : 2 * K ^ 2 * ‖ξ‖ ^ 2 ≤ ((2 * K) * ‖ξ‖) ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg K) (sq_nonneg ‖ξ‖)]
  simpa only [sum_apply] using
    (sq_le_sq₀ (norm_nonneg (∑ p, A p ξ))
      (mul_nonneg (by positivity : 0 ≤ 2 * K) (norm_nonneg ξ))).mp (hsq.trans hlast)

end OrthogonalBoundarySum

section ActualPieces

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (n : ℕ)
  (sets : Fin (n + 1) → Set α) (center : Fin (n + 1))

/-- Actual physical zero extension of the two columns on every model.
Gap pieces are represented by zero columns in this model-only sum. -/
def innerModelColumnSum
    (columns : Fin (n + 1) → Fin 2 → InnerBorderL2 μ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] InnerBorderL2 μ :=
  ∑ p, innerBorderPieceProjection μ sets center p ∘L
    innerTwoColumnMap (columns p) ∘L innerChainBoundaryCLM n p

/-- Uniform model assembly. For the normalized physical columns the
local constant is C/j, so the assembled constant remains 4C/j. -/
theorem innerModelColumnSum_norm_le
    (hmeas : ∀ p, MeasurableSet (sets p))
    (hdis : Pairwise (fun p q => Disjoint (sets p) (sets q)))
    (columns : Fin (n + 1) → Fin 2 → InnerBorderL2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hcol : ∀ p i, ‖columns p i‖ ≤ K) :
    ‖innerModelColumnSum μ n sets center columns‖ ≤ 4 * K := by
  have hsum := norm_innerOrthogonalBoundarySum_le (innerChainBoundaryCLM n)
    (fun p => innerBorderPieceProjection μ sets center p ∘L
      innerTwoColumnMap (columns p) ∘L innerChainBoundaryCLM n p)
    (K := 2 * K) (by positivity) (innerChainBoundary_bessel n)
    (fun ξ p q hpq => innerBorderPieceProjections_orthogonal
      μ sets center hmeas hdis _ _ hpq)
    (fun p ξ => (innerBorderPieceProjection_contract μ sets center hmeas p _).trans
      (((innerTwoColumnMap (columns p)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (innerTwoColumnMap_norm_le (columns p) hK (hcol p))
          (norm_nonneg _))))
  simpa only [innerModelColumnSum, show 2 * (2 * K) = 4 * K by ring] using hsum

end ActualPieces

section WeightedPhysicalAssembly

open scoped MatrixOrder Matrix.Norms.L2Operator

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (n : ℕ)
  (sets : Fin (n + 1) → Set α) (center : Fin (n + 1))
  (columns : Fin (n + 1) → Fin 2 → InnerBorderL2 μ)
  (W : α → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ x, |W x| ≤ CW)
  (w κ : Fin n → ℝ)

/-- These are precisely the actual weighted model columns divided by
their own positive physical cut energies and cut weights. -/
def innerNormalizedModelColumns (p : Fin (n + 1)) (i : Fin 2) : InnerBorderL2 μ :=
  (innerChainScalarRestriction n p w 1 i *
      Real.sqrt (innerChainScalarRestriction n p κ 1 i))⁻¹ •
    innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) (columns p i)

/-- Normalize before summing. The diagonal on the right is the global
cut-energy diagonal, not a collection of unrelated local weights. -/
theorem innerModelColumnSum_weighted_factorization
    (hmeas : ∀ p, MeasurableSet (sets p))
    (hw : ∀ i, 0 < w i) (hκ : ∀ i, 0 < κ i) :
    innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) ∘L
      innerModelColumnSum μ n sets center columns ∘L
        innerBoundaryDiagonal (fun i => (w i)⁻¹) =
      innerModelColumnSum μ n sets center
        (innerNormalizedModelColumns μ n columns W hW CW hWC w κ) ∘L
          innerBoundaryDiagonal (fun i => Real.sqrt (κ i)) := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [innerModelColumnSum, ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [innerBorderPieceProjection_weight_commute μ sets center hmeas W hW CW hWC p,
    innerChainBoundaryCLM_inverse_diagonal, innerChainBoundaryCLM_sqrt_diagonal]
  apply congrArg (innerBorderPieceProjection μ sets center p)
  exact innerTwoColumnMap_weighted_normalization (columns p)
    (innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC))
    (innerChainScalarRestriction n p w 1) (innerChainScalarRestriction n p κ 1)
    (innerChainScalarRestriction_pos n p w hw (by norm_num))
    (innerChainScalarRestriction_pos n p κ hκ (by norm_num)) (innerChainBoundaryCLM n p ξ)

/-- The model contribution has the required uniform j⁻¹ scale once the
actual normalized columns have that scale. Positivity and domination
refer to the full reference matrix, retaining all positive gap blocks. -/
theorem innerModelColumnSum_weighted_normalized_bound
    (hmeas : ∀ p, MeasurableSet (sets p))
    (hdis : Pairwise (fun p q => Disjoint (sets p) (sets q)))
    (hw : ∀ i, 0 < w i) (hκ : ∀ i, 0 < κ i)
    (S₀ : Matrix (Fin n) (Fin n) ℝ) (hS₀ : S₀.PosDef)
    (hdom : Matrix.diagonal κ ≤ S₀) {K j : ℝ} (hK : 0 ≤ K) (hj : 0 < j)
    (hcol : ∀ p i,
      ‖innerNormalizedModelColumns μ n columns W hW CW hWC w κ p i‖ ≤ K / j) :
    ‖(innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) ∘L
      innerModelColumnSum μ n sets center columns ∘L
        innerBoundaryDiagonal (fun i => (w i)⁻¹)) ∘L
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (innerInterfaceInverseSqrt S₀)‖ ≤
      (4 * K) / j := by
  rw [innerModelColumnSum_weighted_factorization μ n sets center columns
    W hW CW hWC w κ hmeas hw hκ, ContinuousLinearMap.comp_assoc]
  have hmodels := innerModelColumnSum_norm_le μ n sets center hmeas hdis
    (innerNormalizedModelColumns μ n columns W hW CW hWC w κ)
    (div_nonneg hK hj.le) hcol
  have hreference := innerBoundaryDiagonal_sqrt_reference_norm_le_one n κ
    (fun i => (hκ i).le) S₀ hS₀ hdom
  calc
    _ ≤ ‖innerModelColumnSum μ n sets center
        (innerNormalizedModelColumns μ n columns W hW CW hWC w κ)‖ *
        ‖innerBoundaryDiagonal (fun i => Real.sqrt (κ i)) ∘L
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (innerInterfaceInverseSqrt S₀)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (4 * (K / j)) * 1 :=
      mul_le_mul hmodels hreference (norm_nonneg _) (by positivity)
    _ = (4 * K) / j := by ring

end WeightedPhysicalAssembly

end ContinuousFlexibility.Radial
