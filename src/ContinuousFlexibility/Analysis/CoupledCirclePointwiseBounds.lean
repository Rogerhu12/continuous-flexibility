import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds

/-!
# Uniform evaluation of the actual weighted circle jets

The estimate keeps one extra power of the sample weight available for a
square-summable majorant. It is uniform in the evaluation angle, so it also
applies after composition with a circle chart.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem coupled_circle_weighted_jet_le_grading
    {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (u : M.Space) (m b c : ℕ) (θ : ℝ) :
    |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv b (M.decode u m) θ| ≤
      anglePairEvaluationConstant * M.grading (b + c + 1) u := by
  have hu := hM.2.2.2.1 u
  have hrow : ‖circleJetEncodeHilbert hu (b + c + 1) m‖ ≤
      M.grading (b + c + 1) u := by
    calc
      _ ≤ ‖circleJetEncodeHilbert hu (b + c + 1)‖ :=
        lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ m
      _ = circleNorm T γ (b + c + 1) (M.decode u) := circleJetEncodeHilbert_norm hu _
      _ = ‖u.val (b + c + 1)‖ := (hM.2.2.2.2.2.2.2 u _).symm
      _ ≤ M.grading (b + c + 1) u := norm_coordinate_le_graded _ _ le_rfl u
  exact (spaces_circle_weighted_pointwise hu _ m b c le_rfl θ).trans
    (mul_le_mul_of_nonneg_left hrow anglePairEvaluationConstant_nonneg)

private theorem coupled_circle_unweight_jet {H γ d B : ℝ}
    (hH : 0 < H) (hd : |H ^ (-γ) * d| ≤ B) :
    |d| ≤ B * H ^ γ := by
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH (-γ)),
    Real.rpow_neg hH.le, ← div_eq_inv_mul] at hd
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hH γ)).mp hd

/-- One constant controls every unweighted angular jet; only the grading
index changes with the derivative order. -/
theorem coupled_circle_jet_uniform_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hγ : 0 < γ) (hM : IsCircleModel T γ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u : M.Space) (m b : ℕ) (θ : ℝ),
      |iteratedDeriv b (M.decode u m) θ| ≤ K * M.grading (b + 1) u := by
  have hEnvelope := hT.2.2.2.2.2.2.2.2.2.2.2.2.1 0 γ hγ
  let H : ℝ := hEnvelope.choose
  have hH : 0 < H := hEnvelope.choose_spec.1
  have hHb : ∀ r ∈ Ioo D.a D.b, T.H r ^ γ * T.M r ^ (0 : ℝ) ≤ H :=
    hEnvelope.choose_spec.2.1
  let K : ℝ := max 1 (anglePairEvaluationConstant * H)
  refine ⟨K, le_max_left _ _, fun u m b θ => ?_⟩
  have hp : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hweight : T.H (T.sample m) ^ γ ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hHb _ (hsample m)
  have hw : |T.H (T.sample m) ^ (-γ) * iteratedDeriv b (M.decode u m) θ| ≤
      anglePairEvaluationConstant * M.grading (b + 1) u := by
    simpa only [pow_zero, one_mul, Nat.add_zero] using
      coupled_circle_weighted_jet_le_grading hM u m b 0 θ
  calc
    _ ≤ (anglePairEvaluationConstant * M.grading (b + 1) u) *
        T.H (T.sample m) ^ γ := coupled_circle_unweight_jet hp hw
    _ ≤ (anglePairEvaluationConstant * M.grading (b + 1) u) * H :=
      mul_le_mul_of_nonneg_left hweight
        (mul_nonneg anglePairEvaluationConstant_nonneg (apply_nonneg _ _))
    _ = (anglePairEvaluationConstant * H) * M.grading (b + 1) u := by ring
    _ ≤ K * M.grading (b + 1) u :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (apply_nonneg _ _)

/-- Reserving one weight order gives the same fixed square-summable
envelope at every derivative order and every evaluation angle. -/
theorem coupled_circle_weighted_jet_envelope
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (hM : IsCircleModel T γ M) (u : M.Space) (m b c : ℕ) (θ : ℝ) :
    |(T.M (T.sample m) ^ c * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv b (M.decode u m) θ| ≤
      (T.M (T.sample m))⁻¹ *
        (anglePairEvaluationConstant * M.grading (b + c + 2) u) := by
  let W : ℝ := T.M (T.sample m)
  have hW : 0 < W := zero_lt_one.trans_le (hT.2.1 _ (hsample m)).2.2.2
  have he : (W ^ c * T.H (T.sample m) ^ (-γ)) *
      iteratedDeriv b (M.decode u m) θ =
      W⁻¹ * ((W ^ (c + 1) * T.H (T.sample m) ^ (-γ)) *
        iteratedDeriv b (M.decode u m) θ) := by
    rw [pow_succ]
    field_simp [hW.ne']
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hW)]
  have hb := coupled_circle_weighted_jet_le_grading hM u m b (c + 1) θ
  have hi : b + (c + 1) + 1 = b + c + 2 := by omega
  rw [hi] at hb
  exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hW.le)

end ContinuousFlexibility.Statements
