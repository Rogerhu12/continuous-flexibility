module

public import ContinuousFlexibility.Analysis.CircleModelRealization
public import ContinuousFlexibility.Analysis.CircleJetClosedGraph
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A single radial control direction in the given circle model

The constant angular field at one sample belongs to every weighted circle
space. Its physical norm has one explicit power of the sample weight. This
keeps the control direction used in optical differentiation tied to the
actual decoder and to the actual projective grading.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff BigOperators ENNReal

def circleSingletonField (m : ℕ) (c : ℝ) : ℕ → ℝ → ℝ :=
  fun n _ => if n = m then c else 0

theorem circleSingletonField_iteratedDeriv (m n b : ℕ) (c θ : ℝ) :
    iteratedDeriv b (circleSingletonField m c n) θ =
      if b = 0 then (if n = m then c else 0) else 0 := by
  exact iteratedDeriv_const

theorem circleSingletonField_energy (T : MaterialData) (γ : ℝ) (s m : ℕ) (c : ℝ) :
    (∑' n : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample n) ^ (j.val 1).val *
        T.H (T.sample n) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleSingletonField m c n))
          2 angleMeasure ^ 2) =
      ∑ j : CircleJetIndex s,
        ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
          T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv (j.val 0).val (fun _ : ℝ => c))
            2 angleMeasure ^ 2 := by
  classical
  let term (n : ℕ) : ℝ≥0∞ :=
    ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample n) ^ (j.val 1).val *
        T.H (T.sample n) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleSingletonField m c n))
          2 angleMeasure ^ 2
  have hzero : ∀ n : ℕ, n ≠ m → term n = 0 := by
    intro n hn
    have hf : circleSingletonField m c n = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      exact if_neg hn
    unfold term
    rw [hf]
    apply Finset.sum_eq_zero
    intro j _
    have hd : iteratedDeriv (j.val 0).val (fun _ : ℝ => (0 : ℝ)) =
        fun _ : ℝ => (0 : ℝ) := by
      funext θ
      exact iteratedDeriv_fun_const_zero
    rw [hd, eLpNorm_fun_zero]
    simp
  have hmain : circleSingletonField m c m = fun _ : ℝ => c := by
    funext θ
    exact if_pos rfl
  have hs : (∑' n : ℕ, term n) = term m := tsum_eq_single m hzero
  simpa only [term, hmain] using hs

theorem circleSingletonField_member (T : MaterialData) (γ : ℝ) (m : ℕ) (c : ℝ) :
    CircleMember T γ (circleSingletonField m c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨contDiff_const, fun _ => rfl⟩
  · intro n b
    exact memLp_angleMeasure_iteratedDeriv_of_contDiff contDiff_const b
  · intro s
    rw [circleSingletonField_energy]
    apply ENNReal.sum_lt_top.mpr
    intro j _
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rw [pow_two]
    have h := (memLp_angleMeasure_iteratedDeriv_of_contDiff
      (show ContDiff ℝ ∞ (fun _ : ℝ => c) from contDiff_const) (j.val 0).val)
    exact ENNReal.mul_lt_top h h

def circleSingletonFieldLinear (m : ℕ) : ℝ →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun := circleSingletonField m
  map_add' := by
    intro c d
    funext n θ
    by_cases hn : n = m <;> simp [circleSingletonField, hn]
  map_smul' := by
    intro c d
    funext n θ
    by_cases hn : n = m <;> simp [circleSingletonField, hn]

def circleSingletonLinear {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) : ℝ →ₗ[ℝ] S.Space :=
  liftCircleLinear hS (circleSingletonFieldLinear m)
    (fun c => circleSingletonField_member T γ m c)

theorem circleSingletonLinear_decode {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) (c : ℝ) :
    S.decode (circleSingletonLinear hS m c) = circleSingletonField m c := by
  exact liftCircleLinear_decode hS (circleSingletonFieldLinear m)
    (fun d => circleSingletonField_member T γ m d) c

theorem circleSingletonLinear_mean {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m n : ℕ) (c : ℝ) :
    angularMean (S.decode (circleSingletonLinear hS m c) n) =
      if n = m then c else 0 := by
  rw [circleSingletonLinear_decode]
  unfold angularMean circleSingletonField
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

private theorem constant_iteratedDeriv_L2_le (b : ℕ) :
    (eLpNorm (iteratedDeriv b (fun _ : ℝ => (1 : ℝ))) 2 angleMeasure).toReal ≤
      (eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure).toReal := by
  by_cases hb : b = 0
  · simp only [hb, iteratedDeriv_zero, le_refl]
  · have hd : iteratedDeriv b (fun _ : ℝ => (1 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      simp only [iteratedDeriv_const, if_neg hb]
    rw [hd, eLpNorm_fun_zero, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

/-- The constant depends only on the output order, not on the sample. -/
def circleSingletonNormConstant (s : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (CircleJetIndex s) : ℝ) *
    (eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure).toReal

theorem circleSingletonNormConstant_nonneg (s : ℕ) :
    0 ≤ circleSingletonNormConstant s :=
  mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg

theorem circleSingletonField_norm_le (T : MaterialData) (γ : ℝ) (s m : ℕ)
    (hM : 1 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    circleNorm T γ s (circleSingletonField m 1) ≤
      circleSingletonNormConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-γ)) := by
  classical
  let R : ℝ := (eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 angleMeasure).toReal
  let W : ℝ := T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-γ)
  have hM0 : 0 ≤ T.M (T.sample m) := le_trans zero_le_one hM
  have hHp : 0 ≤ T.H (T.sample m) ^ (-γ) := Real.rpow_nonneg hH _
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  have hW : 0 ≤ W := mul_nonneg (pow_nonneg hM0 _) hHp
  have hfinite (j : CircleJetIndex s) :
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (fun _ : ℝ => (1 : ℝ)))
          2 angleMeasure ^ 2 ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rw [pow_two]
    have h := (memLp_angleMeasure_iteratedDeriv_of_contDiff
      (show ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) from contDiff_const) (j.val 0).val)
    exact ENNReal.mul_lt_top h h
  have hterm (j : CircleJetIndex s) :
      (T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2 *
        (eLpNorm (iteratedDeriv (j.val 0).val (fun _ : ℝ => (1 : ℝ)))
          2 angleMeasure).toReal ^ 2 ≤ (W * R) ^ 2 := by
    have hj : (j.val 1).val ≤ s := by have := j.property; omega
    have hw := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hj) hHp
    have hw0 : 0 ≤ T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ) :=
      mul_nonneg (pow_nonneg hM0 _) hHp
    have hv := constant_iteratedDeriv_L2_le (j.val 0).val
    have hv0 := ENNReal.toReal_nonneg
      (a := eLpNorm (iteratedDeriv (j.val 0).val (fun _ : ℝ => (1 : ℝ))) 2 angleMeasure)
    have hp : (T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) *
        (eLpNorm (iteratedDeriv (j.val 0).val (fun _ : ℝ => (1 : ℝ)))
          2 angleMeasure).toReal ≤ W * R :=
      mul_le_mul hw hv hv0 hW
    have hp0 := mul_nonneg hw0 hv0
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (add_nonneg (mul_nonneg hW hR) hp0)]
  have he :
      ((∑ j : CircleJetIndex s,
        ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
          T.H (T.sample m) ^ (-γ)) ^ 2) *
          eLpNorm (iteratedDeriv (j.val 0).val (fun _ : ℝ => (1 : ℝ)))
            2 angleMeasure ^ 2).toReal) ≤
        (Fintype.card (CircleJetIndex s) : ℝ) * (W * R) ^ 2 := by
    rw [ENNReal.toReal_sum (fun j _ => hfinite j)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_pow]
    calc
      _ ≤ ∑ _j : CircleJetIndex s, (W * R) ^ 2 := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp
  unfold circleNorm
  rw [circleSingletonField_energy]
  have hs := Real.sqrt_le_sqrt he
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (mul_nonneg hW hR)] at hs
  calc
    _ ≤ Real.sqrt (Fintype.card (CircleJetIndex s) : ℝ) * (W * R) := hs
    _ = circleSingletonNormConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-γ)) := by
      unfold circleSingletonNormConstant W R
      ring


/-- Taking the finite maximum in the projective grading costs a constant
depending only on the chosen order. -/
def circleSingletonGradingConstant (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (s + 1), circleSingletonNormConstant i

theorem circleSingletonGradingConstant_nonneg (s : ℕ) :
    0 ≤ circleSingletonGradingConstant s := by
  exact Finset.sum_nonneg (fun i _ => circleSingletonNormConstant_nonneg i)

theorem circleSingletonLinear_grading_le
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (s m : ℕ)
    (hM : 1 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    S.grading s (circleSingletonLinear hS m 1) ≤
      circleSingletonGradingConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-γ)) := by
  have hHp : 0 ≤ T.H (T.sample m) ^ (-γ) := Real.rpow_nonneg hH _
  have hM0 : 0 ≤ T.M (T.sample m) := le_trans zero_le_one hM
  apply (circleGrading_le_iff_circleNorm hS s _
    (mul_nonneg (circleSingletonGradingConstant_nonneg s)
      (mul_nonneg (pow_nonneg hM0 _) hHp))).mpr
  intro i hi
  rw [circleSingletonLinear_decode]
  have hCi : circleSingletonNormConstant i ≤ circleSingletonGradingConstant s := by
    exact Finset.single_le_sum (fun j _ => circleSingletonNormConstant_nonneg j)
      (Finset.mem_range.mpr (by omega))
  calc
    circleNorm T γ i (circleSingletonField m 1) ≤
        circleSingletonNormConstant i *
          (T.M (T.sample m) ^ i * T.H (T.sample m) ^ (-γ)) :=
      circleSingletonField_norm_le T γ i m hM hH
    _ ≤ circleSingletonGradingConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-γ)) :=
      mul_le_mul hCi
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hi) hHp)
        (mul_nonneg (pow_nonneg hM0 _) hHp)
        (circleSingletonGradingConstant_nonneg s)

end ContinuousFlexibility.Statements
