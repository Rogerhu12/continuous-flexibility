import ContinuousFlexibility.Radial.InnerOrthogonalOperatorSum
import ContinuousFlexibility.Radial.InnerBorderPieceProjection
import ContinuousFlexibility.Radial.InnerBorderWeights

/-!
# Weighted direct sums on the actual bordered source space

The input is split by physical piece projections with its scalar assigned
to the central piece. Distinct weighted outputs are still orthogonal.
The local output loss is kept separate from the input reciprocal weight,
so its coefficient factor is paid only once.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

section HilbertPieces

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def innerProjectedDirichletSum (P D : ι → H →L[ℝ] H) : H →L[ℝ] H :=
  ∑ i, P i ∘L D i ∘L P i

/-- Separate local input and output bounds include the localized loss
without a square root or an additional factor depending on the pieces. -/
theorem innerProjectedDirichletSum_weighted_bound
    (P D : ι → H →L[ℝ] H) (W V : H →L[ℝ] H)
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hsource : ∀ f, (∑ i, ‖P i f‖ ^ 2) ≤ ‖f‖ ^ 2)
    (horth : ∀ i k, i ≠ k → ∀ f g, ⟪P i f, P k g⟫_ℝ = 0)
    (hcontract : ∀ i f, ‖P i f‖ ≤ ‖f‖)
    (hcommute : ∀ i f, W (P i f) = P i (W f))
    (houtput : ∀ i f, ‖W (P i f)‖ ≤ u i * ‖P i f‖)
    (hinput : ∀ i f, ‖P i (V f)‖ ≤ v i * ‖P i f‖)
    {K : ℝ} (hK : 0 ≤ K) (hcost : ∀ i, u i * v i * ‖D i‖ ≤ K) :
    ‖W ∘L innerProjectedDirichletSum P D ∘L V‖ ≤ K := by
  let A : ι → H →L[ℝ] H := fun i => W ∘L P i ∘L D i ∘L P i ∘L V
  have hsum : ‖∑ i, A i‖ ≤ K := by
    apply norm_innerOrthogonalOperatorSum_le P A hK hsource
    · intro f i k hik
      change ⟪W (P i (D i (P i (V f)))), W (P k (D k (P k (V f))))⟫_ℝ = 0
      rw [hcommute, hcommute]
      exact horth i k hik _ _
    · intro i f
      change ‖W (P i (D i (P i (V f))))‖ ≤ K * ‖P i f‖
      calc
        _ ≤ u i * ‖P i (D i (P i (V f)))‖ := houtput i _
        _ ≤ u i * ‖D i (P i (V f))‖ :=
          mul_le_mul_of_nonneg_left (hcontract i _) (hu i)
        _ ≤ u i * (‖D i‖ * ‖P i (V f)‖) :=
          mul_le_mul_of_nonneg_left ((D i).le_opNorm _) (hu i)
        _ ≤ u i * (‖D i‖ * (v i * ‖P i f‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hinput i f) (norm_nonneg _)) (hu i)
        _ = (u i * v i * ‖D i‖) * ‖P i f‖ := by ring
        _ ≤ K * ‖P i f‖ := mul_le_mul_of_nonneg_right (hcost i) (norm_nonneg _)
  have heq : W ∘L innerProjectedDirichletSum P D ∘L V = ∑ i, A i := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [innerProjectedDirichletSum, ContinuousLinearMap.comp_apply,
      sum_apply, map_sum, A]
  rw [heq]
  exact hsum

end HilbertPieces

section ActualBorderPieces

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  (μ : Measure α) (sets : ι → Set α) (center : ι)

theorem innerBorderPieceProjection_contract
    (hmeas : ∀ i, MeasurableSet (sets i)) (i : ι) (F : InnerBorderL2 μ) :
    ‖innerBorderPieceProjection μ sets center i F‖ ≤ ‖F‖ := by
  have hf := (innerL2PieceProjection μ (sets i)).le_opNorm F.fst
  have hpbound : ‖innerL2PieceProjection μ (sets i)‖ * ‖F.fst‖ ≤ 1 * ‖F.fst‖ :=
    mul_le_mul_of_nonneg_right
      (norm_innerL2PieceProjection_le_one μ (sets i) (hmeas i)) (norm_nonneg F.fst)
  have hf' : ‖innerL2PieceProjection μ (sets i) F.fst‖ ≤ ‖F.fst‖ :=
    hf.trans (by simpa only [one_mul] using hpbound)
  have hs : (if i = center then F.snd else 0) ^ 2 ≤ F.snd ^ 2 := by
    split_ifs
    · exact le_rfl
    · simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using sq_nonneg F.snd
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg F)).mp
  rw [innerBorderPieceProjection_norm_sq, innerBorderL2_norm_sq_coordinates]
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hf') hs

theorem innerBorderPieceProjection_weight_commute
    (hmeas : ∀ i, MeasurableSet (sets i))
    (W : α → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ x, |W x| ≤ CW)
    (i : ι) (F : InnerBorderL2 μ) :
    innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC)
      (innerBorderPieceProjection μ sets center i F) =
    innerBorderPieceProjection μ sets center i
      (innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC) F) := by
  simp only [innerBorderPieceProjection_apply, innerBorderFieldMap_apply,
    WithLp.toLp_fst, WithLp.toLp_snd]
  rw [innerL2PieceProjection_weight_commute μ (sets i) (hmeas i) W hW CW hWC]

/-- A physical local multiplier bound includes the scalar if and only if
this piece is the middle piece. Thus tail estimates need not pay one. -/
theorem innerBorderPieceProjection_weight_bound
    (hmeas : ∀ i, MeasurableSet (sets i))
    (W : α → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ x, |W x| ≤ CW)
    (i : ι) {c : ℝ} (hc : 0 ≤ c) (hcenter : i = center → 1 ≤ c)
    (hlocal : ∀ x ∈ sets i, |W x| ≤ c) (F : InnerBorderL2 μ) :
    ‖innerBorderFieldMap μ (innerWeightMultiplier μ W hW CW hWC)
      (innerBorderPieceProjection μ sets center i F)‖ ≤
      c * ‖innerBorderPieceProjection μ sets center i F‖ := by
  have hf := innerWeightMultiplier_norm_le_on_support μ W hW CW hWC (sets i)
    (innerL2PieceProjection μ (sets i) F.fst)
    (innerL2PieceProjection_supported μ (sets i) (hmeas i) F.fst) hlocal
  have hfsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hf
  have hs : (if i = center then F.snd else 0) ^ 2 ≤
      c ^ 2 * (if i = center then F.snd else 0) ^ 2 := by
    by_cases hi : i = center
    · rw [if_pos hi]
      have hc2 : 1 ≤ c ^ 2 := by nlinarith only [hcenter hi]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 (sq_nonneg F.snd)
    · rw [if_neg hi, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  simp only [innerBorderPieceProjection_apply, innerBorderFieldMap_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, innerBorderL2_norm_sq, mul_pow]
  nlinarith only [hfsq, hs]

end ActualBorderPieces

end ContinuousFlexibility.Radial
