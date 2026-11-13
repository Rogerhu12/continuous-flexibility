import ContinuousFlexibility.Analysis.N04NegativeChartInteriorSectorControl
import ContinuousFlexibility.Analysis.ActualNegativeReferenceAiryCoordinate
import ContinuousFlexibility.Analysis.N01ControlLengthBound

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

/-- The original component travel has a material upper bound at either
selected half sample, uniformly before all states and derivative orders. -/
theorem negativeTravel_material_upper (W : N04RealizationStart)
    (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
      W.C.travel m ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  obtain ⟨K, P, hK, hP, ht⟩ := W.through03.1.1.travel_le_actualCell_length
  obtain ⟨C, Q, hC, hQ, hrad⟩ := materialSample_radialE_power_bound W.hT W.radial.1 hP.le
  obtain ⟨B, A, hB, hA, hhost⟩ := n04bActualTypedAtlas_negative_host_sample_E0_power
    W.hT W.hS W.through03 W.field e Q hQ
  let V : ℝ := 1 + |W.D.b - W.D.a|
  have hV : 0 < V := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (abs_nonneg _))
  refine ⟨K * V * C * B, A, mul_pos (mul_pos (mul_pos hK hV) hC) hB, hA,
    fun m side => ?_⟩
  have hends := W.through03.1.1.2.2.2.1.1 m
  have hwidth : W.C.right m - W.C.left m ≤ V := by
    have h := le_abs_self (W.D.b - W.D.a)
    dsimp only [V]
    linarith only [hends.1, hends.2.2, h]
  have hp : 0 ≤ radialE (W.D.cellIndex (W.C.cell m)) ^ P := Real.rpow_nonneg
    (Real.exp_pos _).le P
  calc
    _ ≤ K * radialE (W.D.cellIndex (W.C.cell m)) ^ P *
        (W.C.right m - W.C.left m) := ht m (W.C.cell m) (W.host m)
    _ ≤ K * radialE (W.D.cellIndex (W.C.cell m)) ^ P * V :=
      mul_le_mul_of_nonneg_left hwidth (mul_nonneg hK.le hp)
    _ = K * V * radialE (W.D.cellIndex (W.C.cell m)) ^ P := by ring
    _ ≤ K * V * (C * W.T.E0 (W.T.sample (W.C.cell m)) ^ Q) :=
      mul_le_mul_of_nonneg_left (hrad _) (mul_nonneg hK.le hV.le)
    _ ≤ K * V * (C * (B * W.T.E0 (W.negativeHalfSample e m side) ^ A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hhost (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
          (W.C.cell m) (W.host m)) hC.le) (mul_nonneg hK.le hV.le)
    _ = _ := by ring

/-- The reciprocal of the actual reference travel is polynomial at the
selected half sample, uniformly after any material overlap restriction. -/
theorem NegativeOpticalFactors.interior_referenceTravel_inverse_material
    (F : W.NegativeOpticalFactors e) (ρ : ℕ → Bool → ℝ)
    (hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m)
    (hρb : ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      (ρ m side)⁻¹ ≤ C * W.T.E0 (W.negativeHalfSample e m side) ^ P) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side x,
      x ∈ Icc (ρ m side / 2) (W.negativeOpticalWidth m side) →
      let τ := n04bTravelOrientation (W.C.travel m) side
        (opticalTravel W.D.w (W.C.left m)
          (inwardComponentPoint (W.C.left m) (W.C.right m) side x))
      0 < τ ∧ τ⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  have hexI := F.reference_powers (-(1 / 2 : ℝ))
  let Ci : ℕ → ℝ := hexI.choose
  have hCi := hexI.choose_spec.1
  have hi := hexI.choose_spec.2
  have hexU := F.reference_powers (1 / 2 : ℝ)
  let Cu : ℕ → ℝ := hexU.choose
  have hCu := hexU.choose_spec.1
  have hu := hexU.choose_spec.2
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
    (hρ m side).1 ((hρ m side).2.trans (W.negativeMaterialCollar_bounds m).2.1) hx
    (mul_pos (hCi 0) (Real.rpow_pos_of_pos hEpos _))
    (F.reference_pos m side) (fun t ht => (href t ht).1) (fun t ht => (href t ht).2)
  have hxpos : 0 < x := (half_pos (hρ m side).1).trans_le hx.1
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
        (pow_le_pow_left₀ (inv_nonneg.mpr (hρ m side).1.le) (hbρ m side) 2) (by positivity)
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
