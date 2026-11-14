module

public import ContinuousFlexibility.Analysis.CircleJetPointwiseEnergy
public import ContinuousFlexibility.Analysis.CircleReturnBounded

/-!
# Fixed-chart composition on the actual weighted circle model

The high-order chain rule controls each weighted derivative by one
component energy at one higher order.  Integration and the complete sum
over components therefore preserve every existing circle level.  For a
fixed uniformly smooth circle lift the resulting operator is linear,
continuous, and tame with one angular derivative of loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators NNReal

set_option backward.isDefEq.respectTransparency false

def circleCompositionJetConstant (s : ℕ) (B : ℝ) : ℝ :=
  ∑ b ∈ Finset.range (s + 1), 2 * (b.factorial : ℝ) * circleSobolevConstant * B ^ b

theorem circleCompositionJetConstant_nonneg (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ circleCompositionJetConstant s B := by
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) circleSobolevConstant_nonneg)
    (pow_nonneg hB b)

theorem circleCompositionJetConstant_term_le {s b : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hb : b ≤ s) :
    2 * (b.factorial : ℝ) * circleSobolevConstant * B ^ b ≤
      circleCompositionJetConstant s B := by
  exact Finset.single_le_sum
    (fun i _ => mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) circleSobolevConstant_nonneg)
      (pow_nonneg hB i)) (Finset.mem_range.mpr (by omega))

def circleCompositionNormConstant (s : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
    (Real.pi * circleCompositionJetConstant s B ^ 2))

theorem circleCompositionNormConstant_nonneg (s : ℕ) (B : ℝ) :
    0 ≤ circleCompositionNormConstant s B := Real.sqrt_nonneg _

def circleComposeField (u φ : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m => u m ∘ φ m

theorem circleComposeField_apply (u φ : ℕ → ℝ → ℝ) (m : ℕ) (θ : ℝ) :
    circleComposeField u φ m θ = u m (φ m θ) := rfl

theorem circleWeighted_comp_L2_square_le
    {T : MaterialData} {γ : ℝ} {u : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) {m n k s : ℕ}
    (hM : 0 < T.M (T.sample m)) (hH : 0 < T.H (T.sample m))
    (horder : n + k ≤ s) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i θ, 1 ≤ i → i ≤ s → |iteratedDeriv i φ θ| ≤ B ^ i) :
    (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) ^ 2 *
      (eLpNorm (iteratedDeriv n (u m ∘ φ)) 2 angleMeasure).toReal ^ 2 ≤
        (Real.pi * circleCompositionJetConstant s B ^ 2) *
          (circleComponentEnergy T γ (s + 1) u m).toReal := by
  let w : ℝ := T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)
  let K : ℝ := circleCompositionJetConstant s B
  let E : ℝ := (circleComponentEnergy T γ (s + 1) u m).toReal
  let J : ℝ → ℝ := iteratedDeriv n (u m ∘ φ)
  have hw : 0 < w := mul_pos (pow_pos hM k) (Real.rpow_pos_of_pos hH _)
  have hK : 0 ≤ K := circleCompositionJetConstant_nonneg s hB0
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hJ : Continuous J := ((hu.1 m).1.comp hφ).continuous_iteratedDeriv n (by simp)
  have hpoint (θ : ℝ) : w * |J θ| ≤ K * Real.sqrt E := by
    have h := circleWeighted_comp_iteratedDeriv_abs_le hu hM hH
      (n := n) (k := k) (s := s + 1) (by omega) hφ θ
      (fun i hi hin => hB i θ hi (by omega))
    exact h.trans (mul_le_mul_of_nonneg_right
      (circleCompositionJetConstant_term_le hB0 (by omega)) (Real.sqrt_nonneg _))
  have hpointSq (θ : ℝ) : w ^ 2 * J θ ^ 2 ≤ K ^ 2 * E := by
    have h := mul_le_mul (hpoint θ) (hpoint θ)
      (mul_nonneg hw.le (abs_nonneg _)) (mul_nonneg hK (Real.sqrt_nonneg _))
    simpa only [← pow_two, mul_pow, sq_abs, Real.sq_sqrt hE] using h
  have hEq := Analysis.circle_angleL2_sq_eq_integral hJ
  rw [intervalIntegral.integral_of_le Real.pi_pos.le] at hEq
  change (eLpNorm J 2 angleMeasure).toReal ^ 2 = ∫ θ, J θ ^ 2 ∂angleMeasure at hEq
  have hfi : Integrable (fun θ => w ^ 2 * J θ ^ 2) angleMeasure :=
    ((hJ.pow 2).const_mul (w ^ 2)).integrableOn_Ioc
  have hci : Integrable (fun _ : ℝ => K ^ 2 * E) angleMeasure :=
    continuous_const.integrableOn_Ioc
  calc
    w ^ 2 * (eLpNorm J 2 angleMeasure).toReal ^ 2 =
        ∫ θ, w ^ 2 * J θ ^ 2 ∂angleMeasure := by
      rw [hEq, integral_const_mul]
    _ ≤ ∫ _ : ℝ, K ^ 2 * E ∂angleMeasure :=
      integral_mono hfi hci hpointSq
    _ = (Real.pi * K ^ 2) * E := by
      rw [integral_const]
      simp only [measureReal_def, angleMeasure, Measure.restrict_apply_univ,
        Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul, mul_assoc]

theorem circleComponentEnergy_comp_le
    {T : MaterialData} {γ : ℝ} {u φ : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) (s : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m i θ, 1 ≤ i → i ≤ s → |iteratedDeriv i (φ m) θ| ≤ B ^ i)
    (m : ℕ) :
    circleComponentEnergy T γ s (circleComposeField u φ) m ≤
      ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) *
        (Real.pi * circleCompositionJetConstant s B ^ 2)) *
          circleComponentEnergy T γ (s + 1) u m := by
  let A : ℝ := Real.pi * circleCompositionJetConstant s B ^ 2
  have hA : 0 ≤ A := mul_nonneg Real.pi_pos.le (sq_nonneg _)
  have hE := circleComponentEnergy_lt_top hu (s + 1) m
  have hterm (j : CircleJetIndex s) :
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleComposeField u φ m)) 2 angleMeasure ^ 2 ≤
      ENNReal.ofReal A * circleComponentEnergy T γ (s + 1) u m := by
    have hJ : Continuous (iteratedDeriv (j.val 0).val (circleComposeField u φ m)) :=
      ((hu.1 m).1.comp (hφ m)).continuous_iteratedDeriv _ (by simp)
    have hJfin : eLpNorm (iteratedDeriv (j.val 0).val (circleComposeField u φ m))
        2 angleMeasure < ⊤ := (memLp_angleMeasure_of_continuous hJ).eLpNorm_lt_top
    have hl : ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleComposeField u φ m))
          2 angleMeasure ^ 2 < ⊤ := by
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      rw [pow_two]
      exact ENNReal.mul_lt_top hJfin hJfin
    have hr : ENNReal.ofReal A * circleComponentEnergy T γ (s + 1) u m < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE
    apply (ENNReal.toReal_le_toReal hl.ne hr.ne).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
    exact circleWeighted_comp_L2_square_le hu (hM m) (hH m) j.property (hφ m) hB0 (hB m)
  calc
    circleComponentEnergy T γ s (circleComposeField u φ) m ≤
        ∑ _ : CircleJetIndex s, ENNReal.ofReal A * circleComponentEnergy T γ (s + 1) u m :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) * A) *
        circleComponentEnergy T γ (s + 1) u m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

theorem circleEnergy_comp_le
    {T : MaterialData} {γ : ℝ} {u φ : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) (s : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m i θ, 1 ≤ i → i ≤ s → |iteratedDeriv i (φ m) θ| ≤ B ^ i) :
    (∑' m, circleComponentEnergy T γ s (circleComposeField u φ) m) ≤
      ENNReal.ofReal ((Fintype.card (CircleJetIndex s) : ℝ) *
        (Real.pi * circleCompositionJetConstant s B ^ 2)) *
          ∑' m, circleComponentEnergy T γ (s + 1) u m := by
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun m => circleComponentEnergy_comp_le hu hM hH hφ s hB0 hB m

theorem circleNorm_comp_le
    {T : MaterialData} {γ : ℝ} {u φ : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) (s : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m i θ, 1 ≤ i → i ≤ s → |iteratedDeriv i (φ m) θ| ≤ B ^ i) :
    circleNorm T γ s (circleComposeField u φ) ≤
      circleCompositionNormConstant s B * circleNorm T γ (s + 1) u := by
  have hb := circleEnergy_comp_le hu hM hH hφ s hB0 hB
  have ht := ENNReal.mul_lt_top
    (ENNReal.ofReal_lt_top (r := (Fintype.card (CircleJetIndex s) : ℝ) *
      (Real.pi * circleCompositionJetConstant s B ^ 2))) (hu.2.2 (s + 1))
  have hQ : 0 ≤ (Fintype.card (CircleJetIndex s) : ℝ) *
      (Real.pi * circleCompositionJetConstant s B ^ 2) := by positivity
  have hr := ENNReal.toReal_mono ht.ne hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hQ] at hr
  have hs := Real.sqrt_le_sqrt hr
  rw [Real.sqrt_mul hQ] at hs
  exact hs

/-- A smooth family of circle lifts whose angular derivatives are uniformly
bounded preserves actual weighted circle membership. -/
theorem circleMember_comp_of_uniform_jets
    {T : MaterialData} {γ : ℝ} {u φ : ℕ → ℝ → ℝ}
    (hu : CircleMember T γ u) (hM : ∀ m, 0 < T.M (T.sample m))
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
    (hp : ∀ m θ, φ m (θ + Real.pi) = φ m θ + Real.pi)
    (hjets : ∀ s, ∃ B : ℝ, 0 ≤ B ∧
      ∀ m i θ, 1 ≤ i → i ≤ s → |iteratedDeriv i (φ m) θ| ≤ B ^ i) :
    CircleMember T γ (circleComposeField u φ) := by
  have hreg (m : ℕ) : ContDiff ℝ ∞ (circleComposeField u φ m) :=
    (hu.1 m).1.comp (hφ m)
  refine ⟨fun m => ⟨hreg m, ?_⟩,
    fun m b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hreg m) b, ?_⟩
  · intro θ
    rw [circleComposeField_apply, circleComposeField_apply, hp m θ]
    exact (hu.1 m).2 (φ m θ)
  · intro s
    obtain ⟨B, hB0, hB⟩ := hjets s
    exact (circleEnergy_comp_le hu hM hH hφ s hB0 hB).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu.2.2 (s + 1)))

end ContinuousFlexibility.Statements
