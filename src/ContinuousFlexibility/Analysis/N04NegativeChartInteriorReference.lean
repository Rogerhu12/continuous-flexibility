import ContinuousFlexibility.Analysis.N04NegativeChartInteriorSectorControl
import ContinuousFlexibility.Analysis.ActualNegativeReferenceAiryCoordinate

/-!
# The actual reference travel stays quantitatively positive in the interior

The lower bound uses the original inward integral and the positive
reference optical factor on the same closed half. Every overlap radius
with a material reciprocal bound is allowed. Thus the later root collar
can be chosen from the actual divided odd coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Interval

private theorem inwardIntegral_inverse_bound
    {g : ℝ → ℝ} (hg : Continuous g) {d x ρ M N : ℝ}
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hx : x ∈ Icc (ρ / 2) d) (hM : 0 < M)
    (hgpos : ∀ t ∈ Icc (0 : ℝ) d, 0 < g t)
    (hginv : ∀ t ∈ Icc (0 : ℝ) d, (Real.sqrt (g t))⁻¹ ≤ M)
    (hgupper : ∀ t ∈ Icc (0 : ℝ) d, Real.sqrt (g t) ≤ N) :
    0 < (∫ t in (0 : ℝ)..x, Real.sqrt (t * g t)) ∧
      (∫ t in (0 : ℝ)..x, Real.sqrt (t * g t))⁻¹ ≤ 6 * M * ρ⁻¹ ^ 2 := by
  have hxpos : 0 < x := (half_pos hρ).trans_le hx.1
  have hx' : x ∈ Icc (0 : ℝ) d := ⟨hxpos.le, hx.2⟩
  have havg := airyAverage_bounds_on_nonnegative_interval
    (Real.continuous_sqrt.comp hg) hx' (fun t ht =>
      ⟨inv_le_of_inv_le₀ (Real.sqrt_pos.mpr (hgpos t ht)) (hginv t ht), hgupper t ht⟩)
  have heq := opticalHalf_integral_eq_airyAverage hx'
    (show ∀ t ∈ Icc (0 : ℝ) d, Real.sqrt (g t) = Real.sqrt (g t) from fun _ _ => rfl)
  have hs : ρ / 2 ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    have hhalf : ρ / 2 ≤ 1 := by linarith only [hρone]
    nlinarith only [hρ, hhalf, hx.1]
  have hpower : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hxpos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hp : (ρ / 2) ^ 2 ≤ x ^ (3 / 2 : ℝ) := by
    rw [hpower, pow_two]
    exact mul_le_mul hx.1 hs (half_pos hρ).le hxpos.le
  have hscale := mul_le_mul hp havg.1 (inv_pos.mpr hM).le
    (Real.rpow_nonneg hxpos.le (3 / 2 : ℝ))
  rw [← heq] at hscale
  have hlo : (ρ / 2) ^ 2 * M⁻¹ * (2 / 3 : ℝ) ≤
      ∫ t in (0 : ℝ)..x, Real.sqrt (t * g t) := by linarith only [hscale]
  have hlopos : 0 < (ρ / 2) ^ 2 * M⁻¹ * (2 / 3 : ℝ) := by positivity
  refine ⟨hlopos.trans_le hlo, (inv_anti₀ hlopos hlo).trans_eq ?_⟩
  field_simp [ne_of_gt hρ, ne_of_gt hM]
  <;> ring

namespace N04RealizationStart

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}

/-- The reciprocal of the actual reference travel is polynomial at the
selected half sample, uniformly after any material overlap restriction. -/
theorem NegativeOpticalFactors.interior_referenceTravel_inverse_material
    (F : W.NegativeOpticalFactors e) (ρ : ℕ → ℝ)
    (hρ : ∀ m, 0 < ρ m ∧ ρ m ≤ W.negativeMaterialCollar m)
    (hρb : ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      (ρ m)⁻¹ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side x,
      x ∈ Icc (ρ m / 2) (W.negativeOpticalWidth m side) →
      let τ := n04bTravelOrientation (W.C.travel m) side
        (opticalTravel W.D.w (W.C.left m)
          (inwardComponentPoint (W.C.left m) (W.C.right m) side x))
      0 < τ ∧ τ⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  obtain ⟨Ci, hCi, hi⟩ := F.reference_powers (-(1 / 2 : ℝ))
  obtain ⟨Cu, hCu, hu⟩ := F.reference_powers (1 / 2 : ℝ)
  obtain ⟨Cρ, Pρ, hCρ, hPρ, hbρ⟩ := hρb
  refine ⟨6 * Ci 0 * Cρ ^ 2, Ci 0 + Pρ * 2, by positivity,
    add_nonneg (hCi 0).le (mul_nonneg hPρ (by norm_num)), fun m side x hx => ?_⟩
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  have hE : 1 ≤ E := W.floor _
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have href (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
      (Real.sqrt (F.reference m side t))⁻¹ ≤ Ci 0 * E ^ (Ci 0) ∧
      Real.sqrt (F.reference m side t) ≤ Cu 0 * E ^ (Cu 0) := by
    have hpos := F.reference_pos m side t ht
    have hpow : F.reference m side t ^ (-(1 / 2 : ℝ)) =
        (Real.sqrt (F.reference m side t))⁻¹ := by
      rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
    constructor
    · simpa only [iteratedDeriv_zero, hpow,
        abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hpos))] using hi m side t ht 0
    · simpa only [iteratedDeriv_zero, ← Real.sqrt_eq_rpow,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hu m side t ht 0
  have hraw := inwardIntegral_inverse_bound (F.reference_smooth m side).continuous
    (hρ m).1 ((hρ m).2.trans (W.negativeMaterialCollar_bounds m).2.1) hx
    (mul_pos (hCi 0) (Real.rpow_pos_of_pos hEpos _))
    (F.reference_pos m side) (fun t ht => (href t ht).1) (fun t ht => (href t ht).2)
  have hxpos : 0 < x := (half_pos (hρ m).1).trans_le hx.1
  have htravel := n04b_reference_orientedTravel_inwardIntegral
    W.radial.1.choose_spec.1 W.through03.1.1.2.2.2.1 m side
    (show x ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) from
      ⟨hxpos.le, hx.2.trans (W.negativeOpticalWidth_le_component m side)⟩)
  have hintegral : (∫ t in (0 : ℝ)..x,
      opticalSpeed W.D.w (inwardComponentPoint (W.C.left m) (W.C.right m) side t)) =
      ∫ t in (0 : ℝ)..x, Real.sqrt (t * F.reference m side t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by simpa only [uIcc_of_le hxpos.le] using ht
    change Real.sqrt (n01aOpticalRadicand W.D.w
      (inwardComponentPoint (W.C.left m) (W.C.right m) side t)) = _
    rw [F.reference_divides m side t
      ⟨ht'.1, ht'.2.trans (hx.2.trans (W.negativeOpticalWidth_le_component m side))⟩]
  dsimp only
  rw [htravel, hintegral]
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  calc
    _ ≤ 6 * (Ci 0 * E ^ (Ci 0)) * (Cρ * E ^ Pρ) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr (hρ m).1.le) (hbρ m side) 2) (by positivity)
    _ = (6 * Ci 0 * Cρ ^ 2) * E ^ (Ci 0 + Pρ * 2) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hEpos.le, Real.rpow_add hEpos]
      norm_num only [Nat.cast_ofNat]
      ring

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.interior_referenceTravel_inverse_material'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.interior_referenceTravel_inverse_material
