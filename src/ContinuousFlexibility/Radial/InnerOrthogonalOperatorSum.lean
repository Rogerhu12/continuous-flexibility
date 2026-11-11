import ContinuousFlexibility.Radial.InnerPieceProjection

/-!
# Uniform bounds for actual sums over disjoint inner pieces

The local estimates are squared before summation. This preserves constants
when the number of retained cells changes. The second theorem applies the
Hilbert estimate to restriction and zero extension in the actual L² measure,
including the local weight ratios on both sides of each Dirichlet block.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Orthogonal outputs and a source Bessel estimate give a bound for the
sum of the local operators with exactly the same constant. -/
theorem norm_innerOrthogonalOperatorSum_le
    (P A : ι → H →L[ℝ] H) {K : ℝ} (hK : 0 ≤ K)
    (hsource : ∀ f, (∑ i, ‖P i f‖ ^ 2) ≤ ‖f‖ ^ 2)
    (horth : ∀ f i k, i ≠ k → ⟪A i f, A k f⟫_ℝ = 0)
    (hlocal : ∀ i f, ‖A i f‖ ≤ K * ‖P i f‖) :
    ‖∑ i, A i‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro f
  have hsum : ‖∑ i, A i f‖ ^ 2 = ∑ i, ‖A i f‖ ^ 2 :=
    inner_orthogonal_sum_norm_sq _ (horth f)
  have hsq : ‖∑ i, A i f‖ ^ 2 ≤ (K * ‖f‖) ^ 2 := by
    rw [hsum, mul_pow]
    calc
      _ ≤ ∑ i, K ^ 2 * ‖P i f‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg (A i f)) (mul_nonneg hK (norm_nonneg _))).mpr (hlocal i f)
      _ = K ^ 2 * ∑ i, ‖P i f‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsource f) (sq_nonneg K)
  simpa only [sum_apply] using
    (sq_le_sq₀ (norm_nonneg (∑ i, A i f)) (mul_nonneg hK (norm_nonneg f))).mp hsq

section PhysicalPieces

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (sets : ι → Set α) (hmeas : ∀ i, MeasurableSet (sets i))
  (D : ι → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)

include hmeas

/-- Restrict the source and zero extend the output of each local block. -/
def innerPieceDirichletBlock (i : ι) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  innerL2PieceProjection μ (sets i) ∘L D i ∘L innerL2PieceProjection μ (sets i)

def innerPieceDirichletSum : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ∑ i, innerPieceDirichletBlock μ sets D i

theorem norm_innerPieceProjectedOutput_le (i : ι) :
    ‖innerL2PieceProjection μ (sets i) ∘L D i‖ ≤ ‖D i‖ := by
  calc
    _ ≤ ‖innerL2PieceProjection μ (sets i)‖ * ‖D i‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖D i‖ := mul_le_mul_of_nonneg_right
      (norm_innerL2PieceProjection_le_one μ (sets i) (hmeas i)) (norm_nonneg _)
    _ = _ := one_mul _

/-- The only weight cost is the local reciprocal ratio. Every field and
every support in this estimate is an actual L² object. -/
theorem innerPieceDirichletBlock_weighted_bound
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (R w : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (hw : ∀ i, 0 < w i)
    (hlocalW : ∀ i x, x ∈ sets i → |W x| ≤ R i * w i)
    (hlocalV : ∀ i x, x ∈ sets i → |V x| ≤ R i / w i)
    (i : ι) (f : Lp ℝ 2 μ) :
    ‖innerWeightMultiplier μ W hW CW hWC
      (innerPieceDirichletBlock μ sets D i (innerWeightMultiplier μ V hV CV hVC f))‖ ≤
        (R i) ^ 2 * ‖D i‖ * ‖innerL2PieceProjection μ (sets i) f‖ := by
  have h := innerWeightMultiplier_local_operator_bound μ W hW CW hWC V hV CV hVC
    (sets i) (innerL2PieceProjection μ (sets i) ∘L D i)
    (fun g => innerL2PieceProjection_supported μ (sets i) (hmeas i) (D i g))
    (innerL2PieceProjection μ (sets i) f)
    (innerL2PieceProjection_supported μ (sets i) (hmeas i) f)
    (hR i) (hw i) (hlocalW i) (hlocalV i)
  have heq :
      innerPieceDirichletBlock μ sets D i (innerWeightMultiplier μ V hV CV hVC f) =
      (innerL2PieceProjection μ (sets i) ∘L D i)
        (innerWeightMultiplier μ V hV CV hVC (innerL2PieceProjection μ (sets i) f)) := by
    simp only [innerPieceDirichletBlock, ContinuousLinearMap.comp_apply,
      innerL2PieceProjection_weight_commute μ (sets i) (hmeas i) V hV CV hVC]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_innerPieceProjectedOutput_le μ sets hmeas D i)
      (sq_nonneg _)) (norm_nonneg _))

/-- The actual sum has a uniform weighted bound whenever the individual
coefficient costs have one common upper bound. -/
theorem innerPieceDirichletSum_weighted_bound
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (W V : α → ℝ) (hW : Measurable W) (hV : Measurable V) (CW CV : ℝ)
    (hWC : ∀ x, |W x| ≤ CW) (hVC : ∀ x, |V x| ≤ CV)
    (R w : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (hw : ∀ i, 0 < w i)
    (hlocalW : ∀ i x, x ∈ sets i → |W x| ≤ R i * w i)
    (hlocalV : ∀ i x, x ∈ sets i → |V x| ≤ R i / w i)
    {K : ℝ} (hK : 0 ≤ K) (hcost : ∀ i, (R i) ^ 2 * ‖D i‖ ≤ K) :
    ‖innerWeightMultiplier μ W hW CW hWC ∘L innerPieceDirichletSum μ sets D ∘L
      innerWeightMultiplier μ V hV CV hVC‖ ≤ K := by
  let A : ι → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := fun i =>
    innerWeightMultiplier μ W hW CW hWC ∘L innerPieceDirichletBlock μ sets D i ∘L
      innerWeightMultiplier μ V hV CV hVC
  have hsupp (i : ι) (f : Lp ℝ 2 μ) :
      ∀ᵐ x ∂μ, x ∉ sets i → A i f x = 0 :=
    innerWeightMultiplier_supported μ W hW CW hWC (sets i) _
      (innerL2PieceProjection_supported μ (sets i) (hmeas i) _)
  have hsum : ‖∑ i, A i‖ ≤ K := by
    apply norm_innerOrthogonalOperatorSum_le
      (fun i => innerL2PieceProjection μ (sets i)) A hK
      (innerL2PieceProjections_bessel μ sets hmeas hdis)
    · intro f i k hik
      exact innerL2_disjoint_inner_zero (hdis hik) (A i f) (A k f) (hsupp i f) (hsupp k f)
    · intro i f
      exact (innerPieceDirichletBlock_weighted_bound μ sets hmeas D
        W V hW hV CW CV hWC hVC R w hR hw hlocalW hlocalV i f).trans
          (mul_le_mul_of_nonneg_right (hcost i) (norm_nonneg _))
  have heq :
      innerWeightMultiplier μ W hW CW hWC ∘L innerPieceDirichletSum μ sets D ∘L
        innerWeightMultiplier μ V hV CV hVC = ∑ i, A i := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [innerPieceDirichletSum, ContinuousLinearMap.comp_apply, sum_apply, map_sum, A]
  rw [heq]
  exact hsum

end PhysicalPieces

end ContinuousFlexibility.Radial
