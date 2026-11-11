import ContinuousFlexibility.Radial.InnerRadialReferenceAssembly
import ContinuousFlexibility.Radial.InnerGapWeights

/-!
# Local weighted Poisson energy on the actual model/gap pieces

Model estimates use the actual normalized physical unit columns.
Positive-gap estimates use the actual radial coercivity and the full
gap conormal matrix. A weight constant on the gap cancels its cut
weight exactly. Both computations keep the original local operators.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

theorem innerBoundarySqrt_norm_sq (κ : Fin 2 → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖(WithLp.toLp 2 (fun i => Real.sqrt (κ i) * ξ i) : EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
      ⟪ξ, innerBoundaryDiagonal κ ξ⟫_ℝ := by
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply, PiLp.inner_apply,
    innerBoundaryDiagonal_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, Real.sq_sqrt (hκ i)]
  ring

theorem innerTwoColumnMap_weighted_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : Fin 2 → H) (W : H →L[ℝ] H) (w κ : Fin 2 → ℝ)
    (hw : ∀ i, 0 < w i) (hκ : ∀ i, 0 < κ i) {K j : ℝ}
    (hK : 0 ≤ K) (hj : 0 < j)
    (hp : ∀ i, ‖(w i * Real.sqrt (κ i))⁻¹ • W (p i)‖ ≤ K / j)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖W (innerTwoColumnMap p (WithLp.toLp 2 (fun i => (w i)⁻¹ * ξ i)))‖ ^ 2 ≤
      ((2 * K) / j) ^ 2 * ⟪ξ, innerBoundaryDiagonal κ ξ⟫_ℝ := by
  let normalized : Fin 2 → H := fun i => (w i * Real.sqrt (κ i))⁻¹ • W (p i)
  let η : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i => Real.sqrt (κ i) * ξ i)
  have hn := innerTwoColumnMap_norm_le normalized (div_nonneg hK hj.le) hp
  have hpoint : ‖innerTwoColumnMap normalized η‖ ≤ ((2 * K) / j) * ‖η‖ := by
    calc
      _ ≤ ‖innerTwoColumnMap normalized‖ * ‖η‖ := (innerTwoColumnMap normalized).le_opNorm η
      _ ≤ (2 * (K / j)) * ‖η‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg η)
      _ = ((2 * K) / j) * ‖η‖ := by ring
  rw [innerTwoColumnMap_weighted_normalization p W w κ hw hκ ξ]
  have hsq := (sq_le_sq₀ (norm_nonneg (innerTwoColumnMap normalized η))
    (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hK) hj.le) (norm_nonneg η))).mpr hpoint
  rw [mul_pow] at hsq
  simpa only [normalized, η, innerBoundarySqrt_norm_sq κ (fun i => (hκ i).le) ξ] using hsq

/-- Only active cut coordinates need the same weight; an outer zero
trace imposes no artificial condition on the outer weight convention. -/
theorem innerChainBoundary_inverse_weight_constant (n : ℕ) (p : Fin (n + 1))
    (w : Fin n → ℝ) (c : ℝ)
    (hleft : 0 < p.val → innerChainScalarRestriction n p w 1 0 = c)
    (hright : p.val < n → innerChainScalarRestriction n p w 1 1 = c)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    innerChainBoundaryCLM n p (innerBoundaryDiagonal (fun i => (w i)⁻¹) ξ) =
      c⁻¹ • innerChainBoundaryCLM n p ξ := by
  rw [innerChainBoundaryCLM_inverse_diagonal]
  apply PiLp.ext
  intro i
  simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases i
  · by_cases hp : 0 < p.val
    · rw [hleft hp]
    · have hz : innerChainBoundaryCLM n p ξ 0 = 0 := by
        simp only [innerChainBoundaryCLM_apply, innerChainBoundaryRestriction_apply,
          ite_true, dif_neg hp]
      rw [hz, mul_zero, mul_zero]
  · by_cases hp : p.val < n
    · rw [hright hp]
    · have hz : innerChainBoundaryCLM n p ξ 1 = 0 := by
        simp only [innerChainBoundaryCLM_apply, innerChainBoundaryRestriction_apply,
          show (1 : Fin 2) ≠ 0 by decide, ite_false, dif_neg hp]
      rw [hz, mul_zero, mul_zero]

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)} (A : InnerRadialGapChart D G j central piece)

theorem poisson_weight_cancel (hw : Continuous D.w)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (c : ℝ) (hc : c ≠ 0) (hconstant : EqOn W (fun _ => c) (Ioo (G.left piece) (G.right piece)))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerBorderFieldMap (radialHilbertMeasure D)
      (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
        (A.poisson hw (c⁻¹ • ξ)) = A.poisson hw ξ := by
  rw [A.poisson_apply, A.poisson_apply, innerBorderFieldMap_apply,
    WithLp.toLp_fst, WithLp.toLp_snd]
  apply congrArg (fun u : RadialModeL2 D =>
    (WithLp.toLp 2 (u, (0 : ℝ)) : InnerBorderL2 (radialHilbertMeasure D)))
  exact innerGapPoissonL2_multiplier_cancel D hw (G.left_pos piece) (G.in_core piece)
    (fun r hr => (G.weight_pos piece r (Ioo_subset_Icc_self hr)).le)
    A.columns A.columns_smooth W hW CW hWC c hc hconstant ξ

theorem poisson_energy_nonneg (hw : ContDiff ℝ ∞ D.w) (ξ : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ ⟪ξ, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A.fluxMatrix ξ⟫_ℝ := by
  apply (innerMatrix_toEuclideanCLM_isPositive ?_).inner_nonneg_right
  exact innerGapFluxMatrix_posSemidef (G.left_lt_right piece).le (G.left_pos piece) hw
    A.columns A.columns_smooth A.columns_boundary A.columns_homogeneous
    (G.weight_pos piece) (fun r hr => A.slope_pos.le.trans (A.slope_lower r hr))

theorem poisson_norm_sq_le (hw : ContDiff ℝ ∞ D.w) {s : ℝ} (hs : 0 < s)
    (hslope : s ≤ A.slope) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖A.poisson hw.continuous ξ‖ ^ 2 ≤
      (Real.sqrt (12 / s) / j) ^ 2 *
        ⟪ξ, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A.fluxMatrix ξ⟫_ℝ := by
  have hn := innerGapPoissonL2_norm_le D hw (G.left_lt_right piece).le (G.left_pos piece)
    A.frequency_pos hs (G.in_core piece)
    (fun r hr => (G.weight_pos piece r (Ioo_subset_Icc_self hr)).le)
    A.columns A.columns_smooth A.columns_boundary A.columns_homogeneous
    (G.weight_pos piece) (fun r hr => hslope.trans (A.slope_lower r hr)) ξ
  have hnonneg := A.poisson_energy_nonneg hw ξ
  have hK : 0 ≤ Real.sqrt (12 / s) / j :=
    div_nonneg (Real.sqrt_nonneg _) A.frequency_pos.le
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK
    (Real.sqrt_nonneg _))).mpr hn
  rw [A.poisson_apply, WithLp.norm_toLp_fst]
  simpa only [fieldPoisson, fluxMatrix, innerGapFluxOperator,
    mul_pow, Real.sq_sqrt hnonneg] using hsq

end InnerRadialGapChart

end ContinuousFlexibility.Radial
