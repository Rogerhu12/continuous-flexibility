import ContinuousFlexibility.Analysis.CircleWeightedComposition

/-!
# Weighted membership from actual componentwise pointwise bounds

These estimates keep each circle's complete input energy until the final
sum.  In particular a uniform pointwise estimate with a global seminorm
does not by itself assert square summability over the circles.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators Topology

theorem circleWeighted_L2_square_le_of_pointwise
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    {m b k t : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hv : Continuous (iteratedDeriv b (v m)))
    (hpoint : ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      K * Real.sqrt (circleComponentEnergy T γ t u m).toReal)
    (hM : 0 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) ^ 2 *
      (eLpNorm (iteratedDeriv b (v m)) 2 angleMeasure).toReal ^ 2 ≤
      (Real.pi * K ^ 2) * (circleComponentEnergy T γ t u m).toReal := by
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  let E : ℝ := (circleComponentEnergy T γ t u m).toReal
  let J : ℝ → ℝ := iteratedDeriv b (v m)
  have hw : 0 ≤ w := mul_nonneg (pow_nonneg hM k) (Real.rpow_nonneg hH _)
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hpointSq (θ : ℝ) : w ^ 2 * J θ ^ 2 ≤ K ^ 2 * E := by
    have h := mul_le_mul (hpoint θ) (hpoint θ)
      (mul_nonneg hw (abs_nonneg _)) (mul_nonneg hK (Real.sqrt_nonneg _))
    simpa only [← pow_two, mul_pow, sq_abs, Real.sq_sqrt hE] using h
  have hEq := Analysis.circle_angleL2_sq_eq_integral hv
  rw [intervalIntegral.integral_of_le Real.pi_pos.le] at hEq
  change (eLpNorm J 2 angleMeasure).toReal ^ 2 = ∫ θ, J θ ^ 2 ∂angleMeasure at hEq
  have hfi : Integrable (fun θ => w ^ 2 * J θ ^ 2) angleMeasure :=
    ((hv.pow 2).const_mul (w ^ 2)).integrableOn_Ioc
  have hci : Integrable (fun _ : ℝ => K ^ 2 * E) angleMeasure :=
    continuous_const.integrableOn_Ioc
  calc
    w ^ 2 * (eLpNorm J 2 angleMeasure).toReal ^ 2 =
        ∫ θ, w ^ 2 * J θ ^ 2 ∂angleMeasure := by
      rw [hEq, integral_const_mul]
    _ ≤ ∫ _ : ℝ, K ^ 2 * E ∂angleMeasure :=
      integral_mono hfi hci (Eventually.of_forall hpointSq)
    _ = (Real.pi * K ^ 2) * E := by
      rw [integral_const]
      simp only [measureReal_def, angleMeasure, Measure.restrict_apply_univ,
        Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul, mul_assoc]

theorem circleComponentEnergy_le_of_pointwise
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hv : ∀ m, ContDiff ℝ ∞ (v m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (s t : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ m b k, b + k ≤ s → ∀ θ,
      (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
        |iteratedDeriv b (v m) θ| ≤
      K * Real.sqrt (circleComponentEnergy T γ t u m).toReal)
    (m : ℕ) :
    circleComponentEnergy T γ s v m ≤
      ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * K ^ 2)) *
        circleComponentEnergy T γ t u m := by
  let A : ℝ := Real.pi * K ^ 2
  have hA : 0 ≤ A := mul_nonneg Real.pi_pos.le (sq_nonneg _)
  have hE := circleComponentEnergy_lt_top hu t m
  have hterm (j : CircleJetIndex s) :
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 ≤
      ENNReal.ofReal A * circleComponentEnergy T γ t u m := by
    have hJ := (hv m).continuous_iteratedDeriv (j.val 0).val (by simp)
    have hJfin := (memLp_angleMeasure_of_continuous hJ).eLpNorm_lt_top
    have hl : ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (v m)) 2 angleMeasure ^ 2 < ⊤ := by
      simpa only [pow_two] using ENNReal.mul_lt_top
        (ENNReal.ofReal_lt_top (r := (T.M (T.sample m) ^ (j.val 1).val *
          T.H (T.sample m) ^ (-γ)) ^ 2)) (ENNReal.mul_lt_top hJfin hJfin)
    have hr : ENNReal.ofReal A * circleComponentEnergy T γ t u m < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE
    apply (ENNReal.toReal_le_toReal hl.ne hr.ne).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
    exact circleWeighted_L2_square_le_of_pointwise hK hJ
      (hpoint m _ _ j.property) (hM m) (hH m)
  calc
    circleComponentEnergy T γ s v m ≤
        ∑ _ : CircleJetIndex s, ENNReal.ofReal A * circleComponentEnergy T γ t u m :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) * A) *
        circleComponentEnergy T γ t u m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

theorem circleMember_of_component_pointwise
    {T : MaterialData} {γ : ℝ} {u v : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u)
    (hv : ∀ m, ContDiff ℝ ∞ (v m) ∧ Function.Periodic (v m) Real.pi)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hpoint : ∀ s, ∃ t : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ m b k, b + k ≤ s → ∀ θ,
        (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
          |iteratedDeriv b (v m) θ| ≤
        K * Real.sqrt (circleComponentEnergy T γ t u m).toReal) :
    CircleMember T γ v := by
  refine ⟨hv, fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hv m).1 b, ?_⟩
  intro s
  obtain ⟨t, K, hK, hpoint⟩ := hpoint s
  let A : ℝ≥0∞ :=
    ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * K ^ 2))
  have henergy : (∑' m, circleComponentEnergy T γ s v m) ≤
      A * ∑' m, circleComponentEnergy T γ t u m := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun m =>
      circleComponentEnergy_le_of_pointwise hu (fun i => (hv i).1) hM hH s t hK hpoint m
  exact henergy.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu.2.2 t))

end ContinuousFlexibility.Statements
