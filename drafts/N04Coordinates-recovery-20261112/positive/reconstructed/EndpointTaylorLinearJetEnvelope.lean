import ContinuousFlexibility.Analysis.EndpointTaylorPolynomialEnvelope

/-!
# Linear high-order data bounds at the already chosen Taylor width

The width cost and the size of the boundary data are separate. Scaling
the actual finite Taylor correction gives a bound linear in the latter,
while preserving the same width for every requested output order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

/-- The displayed endpoint correction is homogeneous in its prescribed
boundary data. Both endpoints use the same polynomial identity. -/
theorem endpointTaylorCorrection_const_mul (n : ℕ) (l r δ t : ℝ)
    (A : Bool → ℕ → ℝ → ℝ) :
    endpointTaylorCorrection n l r δ (fun side j θ => t * A side j θ) =
      fun p => t * endpointTaylorCorrection n l r δ A p := by
  have hpoly (c : ℝ) (side : Bool) (p : PolarPoint) :
      boundaryTaylorPolynomial n c (fun j θ => t * A side j θ) p =
        t * boundaryTaylorPolynomial n c (A side) p := by
    simp only [boundaryTaylorPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  funext p
  simp only [endpointTaylorCorrection, hpoly]
  ring

/-- The constant is chosen before the low width cost `U` and the high
boundary-data bound `B`. The bound does not replace the width by a new
one depending on the requested derivative order or on `B`. -/
theorem exists_endpointTaylorCorrection_linear_jet_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U B δ : ℝ},
      1 ≤ U → 0 < B → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ U →
      ∀ (l r : ℝ) (A : Bool → ℕ → ℝ → ℝ),
      (∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j)) →
      (∀ side j, j ≤ n → ∀ b, b ≤ N → ∀ θ,
        |iteratedDeriv b (A side j) θ| ≤ B) →
      ∀ k, k ≤ N → ∀ p : PolarPoint,
        ‖iteratedFDeriv ℝ k (endpointTaylorCorrection n l r δ A) p‖ ≤
          C * U ^ (N + 1) * B := by
  obtain ⟨C, hC, hbound⟩ := exists_endpointTaylorCorrection_polynomial_envelope n N
  refine ⟨C, hC, ?_⟩
  intro U B δ hU hB hδ hδone hδinv l r A hA hcoeff k hk p
  let D : Bool → ℕ → ℝ → ℝ := fun side j θ => B⁻¹ * A side j θ
  have hD (side : Bool) (j : ℕ) (hj : j ≤ n) : ContDiff ℝ ∞ (D side j) :=
    contDiff_const.mul (hA side j hj)
  have hDcoeff (side : Bool) (j : ℕ) (hj : j ≤ n)
      (b : ℕ) (hb : b ≤ N) (θ : ℝ) :
      |iteratedDeriv b (D side j) θ| ≤ U := by
    dsimp only [D]
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left
        (hcoeff side j hj b hb θ) (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB.ne'
      _ ≤ U := hU
  have hscale : (fun side j θ => B * D side j θ) = A := by
    funext side j θ
    dsimp only [D]
    rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  have he := endpointTaylorCorrection_const_mul n l r δ B D
  rw [hscale] at he
  have hE := contDiff_endpointTaylorCorrection hD l r δ
  rw [he]
  change ‖iteratedFDeriv ℝ k (fun q => B • endpointTaylorCorrection n l r δ D q) p‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((hE.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt),
    norm_smul, Real.norm_eq_abs, abs_of_pos hB]
  exact (mul_le_mul_of_nonneg_left
    (hbound hU hδ hδone hδinv l r D hD hDcoeff k hk p) hB.le).trans_eq (by ring)

end ContinuousFlexibility.Analysis
