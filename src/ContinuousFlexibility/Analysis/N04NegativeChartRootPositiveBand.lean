import ContinuousFlexibility.Analysis.N04NegativeChartRootAxisValues
import ContinuousFlexibility.Analysis.RootOddUniformValueInterval

/-!
# A quantitative positive band for the actual odd coefficient

The radius is explicit and is selected before the state and finite plot.
Its reciprocal pays only the actual inverse root scale, the actual axis
material cost, and the same inverse-coordinate low-jet bound. No target
coefficient lower bound is introduced as a hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

def negativeChartPositiveRadius (κ M : ℝ) : ℝ :=
  (1 + 2 * (M + 1) * κ⁻¹)⁻¹

theorem negativeChartPositiveRadius_bounds {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) :
    0 < negativeChartPositiveRadius κ M ∧ negativeChartPositiveRadius κ M ≤ 1 ∧
      (negativeChartPositiveRadius κ M)⁻¹ = 1 + 2 * (M + 1) * κ⁻¹ ∧
      M * negativeChartPositiveRadius κ M ≤ κ / 2 := by
  have hMp : 0 < M + 1 := by linarith only [hM]
  have hD : 1 ≤ 1 + 2 * (M + 1) * κ⁻¹ :=
    le_add_of_nonneg_right (by positivity)
  have hpos : 0 < negativeChartPositiveRadius κ M :=
    inv_pos.mpr (zero_lt_one.trans_le hD)
  have hsmall : negativeChartPositiveRadius κ M ≤ κ / (2 * (M + 1)) := by
    have hb : (κ / (2 * (M + 1)))⁻¹ ≤ 1 + 2 * (M + 1) * κ⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
      exact le_add_of_nonneg_left zero_le_one
    have hh := inv_anti₀ (inv_pos.mpr (div_pos hκ (by positivity))) hb
    simpa only [inv_inv, negativeChartPositiveRadius] using hh
  refine ⟨hpos, inv_le_one_of_one_le₀ hD,
    (by simp only [negativeChartPositiveRadius, inv_inv]), ?_⟩
  calc
    _ ≤ (M + 1) * negativeChartPositiveRadius κ M :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hpos.le
    _ ≤ (M + 1) * (κ / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hsmall hMp.le
    _ = κ / 2 := by field_simp [hMp.ne'] <;> ring

private theorem rootOdd_positive_radius :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ × ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ G →
      (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) →
      ∀ M : ℝ, 0 ≤ M → ∀ κ : ℝ, 0 < κ →
      CSBound 2 (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M →
      (∀ θ, κ ≤ rootOddCoefficient G (0, θ)) →
      ∀ x ∈ Icc (0 : ℝ) (negativeChartPositiveRadius κ (C * M)), ∀ θ,
        extendedRootOddCoefficient G (x, θ) ∈ Icc (κ / 2) (1 + C * M) := by
  obtain ⟨C, hC, hbound⟩ := exists_csBound_extendedRootOddCoefficient 1
  refine ⟨C, hC, fun G hG hperiod M hM κ hκ hB hzero x hx θ => ?_⟩
  have hCM := mul_nonneg hC.le hM
  have hrad := negativeChartPositiveRadius_bounds hκ hCM
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) Real.pi :=
    fun r _ => rootOddCoefficient_periodic hperiod r
  have hper : ∀ r, Function.Periodic (fun η => extendedRootOddCoefficient G (r, η)) Real.pi :=
    fun r η => seeleyPeriodicExtension_periodic hχperiod r η
  have hv := periodicScalar_radial_value_control
    (contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero hχperiod) hper
    (hbound G hG Real.pi Real.pi_ne_zero hχperiod M hB)
    ⟨hx.1, hx.2.trans hrad.2.1⟩ θ
  have hz : κ ≤ extendedRootOddCoefficient G (0, θ) := by
    rw [extendedRootOddCoefficient_of_nonneg G (p := (0, θ)) le_rfl]
    exact hzero θ
  have hdiff := (abs_le.mp hv.2).1
  have hcost := (mul_le_mul_of_nonneg_left hx.2 hCM).trans hrad.2.2.2
  exact ⟨by linarith only [hdiff, hcost, hz],
    (le_abs_self _).trans (hv.1.trans (le_add_of_nonneg_left zero_le_one))⟩

namespace N04RealizationStart

variable (W : N04RealizationStart)

def negativeRootPositiveRadius (e : ℕ ≃ N04PieceIndex W.D)
    (B p C M δ : ℝ) (m : ℕ) (side : Bool) : ℝ :=
  negativeChartPositiveRadius
    (B * (δ⁻¹) ^ 2 * W.T.E0 (W.negativeHalfSample e m side) ^ p)⁻¹ (C * M)

/-- The chosen scale and the actual low input bound pay the whole
inverse radius at the original selected half sample. -/
theorem negativeRootPositiveRadius_inverse_material
    (e : ℕ ≃ N04PieceIndex W.D) (m : ℕ) (side : Bool)
    {B p C M δ D q K r : ℝ}
    (hB : 0 < B) (hp : 0 ≤ p) (hC : 0 < C) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hD : 0 < D) (hq : 0 ≤ q) (hK : 0 < K) (hr : 0 ≤ r)
    (hδcost : δ⁻¹ ≤ D * W.T.E0 (W.negativeHalfSample e m side) ^ q)
    (hMcost : M ≤ K * W.T.E0 (W.negativeHalfSample e m side) ^ r) :
    (W.negativeRootPositiveRadius e B p C M δ m side)⁻¹ ≤
      (1 + 2 * (C * K + 1) * B * D ^ 2) *
        W.T.E0 (W.negativeHalfSample e m side) ^ (r + q * 2 + p) := by
  let E := W.T.E0 (W.negativeHalfSample e m side)
  have hE : 1 ≤ E := W.floor _
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hMp : 0 ≤ C * M + 1 := by positivity
  have haug : C * M + 1 ≤ (C * K + 1) * E ^ r := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hMcost hC.le) (Real.one_le_rpow hE hr)
    exact hh.trans_eq (by ring)
  have hpow : (δ⁻¹) ^ 2 ≤ D ^ 2 * E ^ (q * 2) := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδcost 2
    change (δ⁻¹) ^ 2 ≤ (D * E ^ q) ^ 2 at hh
    simpa only [mul_pow, ← Real.rpow_mul_natCast hEp.le, Nat.cast_ofNat] using hh
  have hcost : 2 * (C * M + 1) * (B * (δ⁻¹) ^ 2 * E ^ p) ≤
      2 * ((C * K + 1) * E ^ r) * (B * (D ^ 2 * E ^ (q * 2)) * E ^ p) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haug (by norm_num))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB.le)
        (Real.rpow_nonneg hEp.le _))
      (by positivity) (by positivity)
  calc
    _ = 1 + 2 * (C * M + 1) * (B * (δ⁻¹) ^ 2 * E ^ p) := by
      simp only [negativeRootPositiveRadius, negativeChartPositiveRadius, inv_inv, E]
    _ ≤ E ^ (r + q * 2 + p) +
        2 * ((C * K + 1) * E ^ r) * (B * (D ^ 2 * E ^ (q * 2)) * E ^ p) :=
      add_le_add (Real.one_le_rpow hE (by positivity)) hcost
    _ = _ := by
      rw [Real.rpow_add hEp, Real.rpow_add hEp]
      ring

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- The only numerical input concerning the flow is its genuine second
spatial jet bound. The axis lower bound is derived from the actual
coefficients, the actual label, and that same flow package. -/
theorem fullHalfFields_root_positive_band :
    ∃ B p C : ℝ, 0 < B ∧ 0 < p ∧ 0 < C ∧ ∀ n : ℕ,
      ∀ d c : (Fin n → ℝ) × PolarPoint → ℝ,
      ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      (∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi) →
      (∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ A : NegativeChartRootFlowData d c δ,
      ∀ m side M, 0 ≤ M →
        0 < W.negativeRootPositiveRadius e B p C M δ m side ∧
        W.negativeRootPositiveRadius e B p C M δ m side ≤ 1 ∧
        (W.negativeRootPositiveRadius e B p C M δ m side)⁻¹ =
          1 + 2 * (C * M + 1) *
            (B * (δ⁻¹) ^ 2 * W.T.E0 (W.negativeHalfSample e m side) ^ p) ∧
        ∀ (y : Fin n → ℝ) (z : AnnularState W.S × ℝ),
        z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2) → stateSector W.S z.1 →
        (∀ θ, c (y, (0, θ)) = F.fullHalfSpeed z m side (0, θ)) →
        CSBound 2 (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
          (W.negativeRootInverseCoordinate A z m side y) M →
        ∀ x ∈ Icc (0 : ℝ) (W.negativeRootPositiveRadius e B p C M δ m side), ∀ θ,
          extendedRootOddCoefficient (W.negativeRootInverseCoordinate A z m side y) (x, θ) ∈
            Icc ((B * (δ⁻¹) ^ 2 * W.T.E0 (W.negativeHalfSample e m side) ^ p)⁻¹ / 2)
              (1 + C * M) := by
  have hAxis := F.fullHalfFields_root_axis_inverse_material
  let B := hAxis.choose
  let p := hAxis.choose_spec.choose
  have hB := hAxis.choose_spec.choose_spec.1
  have hp := hAxis.choose_spec.choose_spec.2.1
  have haxis := hAxis.choose_spec.choose_spec.2.2
  have hBand := rootOdd_positive_radius
  let C := hBand.choose
  have hC := hBand.choose_spec.1
  have hband := hBand.choose_spec.2
  refine ⟨B, p, C, hB, hp, hC, ?_⟩
  intro n d c hd hc hdp hcp δ hδ hδone A m side M hM
  let κ : ℝ := (B * (δ⁻¹) ^ 2 * W.T.E0 (W.negativeHalfSample e m side) ^ p)⁻¹
  have hE : 0 < W.T.E0 (W.negativeHalfSample e m side) := zero_lt_one.trans_le (W.floor _)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hr := negativeChartPositiveRadius_bounds hκ (mul_nonneg hC.le hM)
  refine ⟨hr.1, hr.2.1, ?_, ?_⟩
  · simpa only [negativeRootPositiveRadius, κ, inv_inv] using hr.2.2.1
  · intro y z hz hs hrep hb
    have hz' : z ∈ stateNeighborhood W.S W.C W.base W.ε :=
      stateNeighborhood_mono W.S W.C le_rfl (by linarith only [W.ε_pos]) hz
    have hregular := W.negativeRootInverseCoordinate_regular hd hc hdp hcp A y hz' hs m side
    apply hband _ hregular.1 hregular.2 M hM κ hκ hb
    intro θ
    have hh := haxis n d c hd hc hdp hcp δ hδ hδone A y z hz hs m side hrep θ
    have hi := inv_anti₀ (inv_pos.mpr hh.1) hh.2
    simpa only [inv_inv] using hi

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_root_positive_band'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_root_positive_band
