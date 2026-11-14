import ContinuousFlexibility.Analysis.N04NegativeChartRootScale
import ContinuousFlexibility.Analysis.N04NegativeChartRootPositiveBand

/-!
# One overlap radius before all derivative orders

The physical overlap radius is the product of the actual root scale and
its positive normalized band. Both reciprocals have material bounds at
the same selected half sample. This radius can therefore be used by the
root estimates and the interior estimates without an order-dependent
choice of neighborhoods.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements

variable (W : N04RealizationStart)

def negativeChartOverlapRadius (e : ℕ ≃ N04PieceIndex W.D)
    (C B p Cχ B₀ p₀ : ℝ) (m : ℕ) (side : Bool) : ℝ :=
  let δ := W.negativeChartRootScale e C m side
  δ * W.negativeRootPositiveRadius e B p Cχ
    (B₀ * W.T.E0 (W.negativeHalfSample e m side) ^ p₀) δ m side

theorem negativeChartOverlapRadius_bounds (e : ℕ ≃ N04PieceIndex W.D)
    {C B p Cχ B₀ p₀ : ℝ}
    (hC : 1 ≤ C) (hB : 0 < B) (hCχ : 0 < Cχ) (hB₀ : 0 < B₀)
    (m : ℕ) (side : Bool) :
    0 < W.negativeChartOverlapRadius e C B p Cχ B₀ p₀ m side ∧
      W.negativeChartOverlapRadius e C B p Cχ B₀ p₀ m side ≤
        W.negativeMaterialCollar m := by
  let δ := W.negativeChartRootScale e C m side
  let E := W.T.E0 (W.negativeHalfSample e m side)
  have hδ := W.negativeChartRootScale_bounds e hC m side
  have hE : 0 < E := zero_lt_one.trans_le (W.floor _)
  have hκ : 0 < (B * (δ⁻¹) ^ 2 * E ^ p)⁻¹ := by
    have hd : 0 < δ := hδ.1
    positivity
  have hM : 0 ≤ Cχ * (B₀ * E ^ p₀) := by positivity
  have hσ := negativeChartPositiveRadius_bounds hκ hM
  have hσpos : 0 < W.negativeRootPositiveRadius e B p Cχ (B₀ * E ^ p₀) δ m side := hσ.1
  have hσone : W.negativeRootPositiveRadius e B p Cχ (B₀ * E ^ p₀) δ m side ≤ 1 := hσ.2.1
  refine ⟨mul_pos hδ.1 hσpos, ?_⟩
  have hdcol : δ ≤ W.negativeMaterialCollar m := by
    have hh := hδ.2.2.1
    have hd : 0 < δ := hδ.1
    change δ * 2 ≤ W.negativeMaterialCollar m at hh
    linarith only [hh, hd]
  exact (mul_le_of_le_one_right hδ.1.le hσone).trans hdcol

/-- The inverse overlap cost uses only the already selected scale and
the fixed low input bound. In particular, its exponent precedes every
state and spatial order of the subsequent chart estimates. -/
theorem negativeChartOverlapRadius_inverse_material (e : ℕ ≃ N04PieceIndex W.D)
    {C B p Cχ B₀ p₀ : ℝ}
    (hC : 1 ≤ C) (hB : 0 < B) (hp : 0 ≤ p)
    (hCχ : 0 < Cχ) (hB₀ : 0 < B₀) (hp₀ : 0 ≤ p₀) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m side,
      (W.negativeChartOverlapRadius e C B p Cχ B₀ p₀ m side)⁻¹ ≤
        K * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  have hex := W.negativeChartRootScale_inverse_material e hC
  let D := hex.choose
  let q := hex.choose_spec.choose
  have hD : 0 < D := hex.choose_spec.choose_spec.1
  have hq : 0 ≤ q := hex.choose_spec.choose_spec.2.1
  have hcost := hex.choose_spec.choose_spec.2.2
  let K : ℝ := 1 + 2 * (Cχ * B₀ + 1) * B * D ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨D * K, q + (p₀ + q * 2 + p), mul_pos hD hK,
    by positivity, fun m side => ?_⟩
  let δ := W.negativeChartRootScale e C m side
  let E := W.T.E0 (W.negativeHalfSample e m side)
  have hδ : 0 < δ := (W.negativeChartRootScale_bounds e hC m side).1
  have hE : 0 < E := zero_lt_one.trans_le (W.floor _)
  have hσ := W.negativeRootPositiveRadius_inverse_material e m side hB hp hCχ
    (show 0 ≤ B₀ * E ^ p₀ by positivity) hδ hD hq hB₀ hp₀ (hcost m side) le_rfl
  have hb := mul_le_mul (hcost m side) hσ
    (inv_nonneg.mpr ((negativeChartPositiveRadius_bounds
      (show 0 < (B * (δ⁻¹) ^ 2 * E ^ p)⁻¹ by positivity)
      (show 0 ≤ Cχ * (B₀ * E ^ p₀) by positivity)).1.le))
    (mul_nonneg hD.le (Real.rpow_nonneg hE.le q))
  change δ⁻¹ * (W.negativeRootPositiveRadius e B p Cχ (B₀ * E ^ p₀) δ m side)⁻¹ ≤
    (D * E ^ q) * (K * E ^ (p₀ + q * 2 + p)) at hb
  calc
    _ = δ⁻¹ * (W.negativeRootPositiveRadius e B p Cχ (B₀ * E ^ p₀) δ m side)⁻¹ := by
      simp only [negativeChartOverlapRadius, mul_inv_rev, δ, E, mul_comm]
    _ ≤ (D * E ^ q) * (K * E ^ (p₀ + q * 2 + p)) := hb
    _ = _ := by
      change (D * E ^ q) * (K * E ^ (p₀ + q * 2 + p)) =
        (D * K) * E ^ (q + (p₀ + q * 2 + p))
      rw [Real.rpow_add hE q (p₀ + q * 2 + p)]
      ring

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeChartOverlapRadius_inverse_material'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeChartOverlapRadius_inverse_material
