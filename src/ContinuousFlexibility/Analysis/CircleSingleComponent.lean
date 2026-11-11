import ContinuousFlexibility.Analysis.CircleEnergyEnvelope
import ContinuousFlexibility.Analysis.CircleSingletonControl

/-!
# Smooth angular fields supported on a single circle

Varying one return radius only changes its actual circle component.
This elementary finite-support realization is used for local spatial
regularity; no uniformity in the chosen component is asserted or needed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff ENNReal BigOperators

def circleSingleComponentField (m : ℕ) (f : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun i θ => if i = m then f θ else 0

def circleSingleComponentFieldLinear (m : ℕ) :
    (ℝ → ℝ) →ₗ[ℝ] (ℕ → ℝ → ℝ) where
  toFun := circleSingleComponentField m
  map_add' := by
    intro f g
    funext i θ
    by_cases hi : i = m <;> simp [circleSingleComponentField, hi]
  map_smul' := by
    intro c f
    funext i θ
    by_cases hi : i = m <;> simp [circleSingleComponentField, hi]

theorem circleSingleComponentField_self (m : ℕ) (f : ℝ → ℝ) :
    circleSingleComponentField m f m = f := by
  funext θ
  exact if_pos rfl

theorem circleSingleComponentField_ne (m i : ℕ) (f : ℝ → ℝ) (hi : i ≠ m) :
    circleSingleComponentField m f i = fun _ => 0 := by
  funext θ
  exact if_neg hi

theorem circleSingleComponentField_iteratedDeriv
    (m i b : ℕ) (f : ℝ → ℝ) (θ : ℝ) :
    iteratedDeriv b (circleSingleComponentField m f i) θ =
      if i = m then iteratedDeriv b f θ else 0 := by
  by_cases hi : i = m
  · subst i
    rw [circleSingleComponentField_self, if_pos rfl]
  · rw [circleSingleComponentField_ne m i f hi, if_neg hi]
    exact iteratedDeriv_fun_const_zero

theorem circleSingleComponentField_energy
    (T : MaterialData) (γ : ℝ) (m s : ℕ) (f : ℝ → ℝ) :
    (∑' i, circleComponentEnergy T γ s (circleSingleComponentField m f) i) =
      circleComponentEnergy T γ s (circleSingleComponentField m f) m := by
  apply tsum_eq_single m
  intro i hi
  unfold circleComponentEnergy
  apply Finset.sum_eq_zero
  intro b hb
  have heq : iteratedDeriv (b.val 0).val (circleSingleComponentField m f i) =
      fun _ => 0 := by
    funext θ
    simp only [circleSingleComponentField_iteratedDeriv, if_neg hi]
  rw [heq, eLpNorm_fun_zero]
  simp

theorem circleSingleComponentField_member
    (T : MaterialData) (γ : ℝ) (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f Real.pi) :
    CircleMember T γ (circleSingleComponentField m f) := by
  have hreg (i : ℕ) : ContDiff ℝ ∞ (circleSingleComponentField m f i) ∧
      Function.Periodic (circleSingleComponentField m f i) Real.pi := by
    by_cases hi : i = m
    · subst i
      rw [circleSingleComponentField_self]
      exact ⟨hf, hper⟩
    · rw [circleSingleComponentField_ne m i f hi]
      exact ⟨contDiff_const, fun _ => rfl⟩
  refine ⟨hreg, fun i b => memLp_angleMeasure_iteratedDeriv_of_contDiff (hreg i).1 b, ?_⟩
  intro s
  rw [circleSingleComponentField_energy]
  unfold circleComponentEnergy
  apply ENNReal.sum_lt_top.mpr
  intro b hb
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  rw [pow_two]
  have h := (memLp_angleMeasure_iteratedDeriv_of_contDiff (hreg m).1 (b.val 0).val).eLpNorm_lt_top
  exact ENNReal.mul_lt_top h h

theorem circleSingleComponentField_norm_le
    {T : MaterialData} {γ : ℝ}
    (hM : ∀ i, 0 ≤ T.M (T.sample i)) (hH : ∀ i, 0 ≤ T.H (T.sample i))
    (m s : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ b ≤ s, ∀ θ, |iteratedDeriv b f θ| ≤ A) :
    circleNorm T γ s (circleSingleComponentField m f) ≤
      (Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * Real.pi) *
        (max 1 (T.M (T.sample m))) ^ s * T.H (T.sample m) ^ (-γ)) * A := by
  classical
  let E : ℕ → ℝ≥0∞ := fun i => if i = m then 1 else 0
  let W : ℝ := (max 1 (T.M (T.sample m))) ^ s * T.H (T.sample m) ^ (-γ)
  have hW : 0 ≤ W := mul_nonneg
    (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.rpow_nonneg (hH m) _)
  have hE : (∑' i, E i) = 1 := by
    rw [tsum_eq_single m (fun i hi => by simp only [E, if_neg hi])]
    simp only [E, if_pos rfl]
  have hreg (i : ℕ) : ContDiff ℝ ∞ (circleSingleComponentField m f i) := by
    by_cases hi : i = m
    · subst i
      rw [circleSingleComponentField_self]
      exact hf
    · rw [circleSingleComponentField_ne m i f hi]
      exact contDiff_const
  have hb (i b k : ℕ) (hbk : b + k ≤ s) (θ : ℝ) :
      (T.M (T.sample i) ^ k * T.H (T.sample i) ^ (-γ)) *
          |iteratedDeriv b (circleSingleComponentField m f i) θ| ≤
        (W * A) * Real.sqrt (E i).toReal := by
    by_cases hi : i = m
    · subst i
      simp only [circleSingleComponentField_iteratedDeriv, if_pos rfl, E,
        ENNReal.toReal_one, Real.sqrt_one, mul_one]
      have hk : T.M (T.sample m) ^ k ≤ (max 1 (T.M (T.sample m))) ^ s :=
        (pow_le_pow_left₀ (hM m) (le_max_right _ _) k).trans
          (pow_le_pow_right₀ (le_max_left _ _) (by omega))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (hH m) _))
        (hbound b (by omega) θ) (abs_nonneg _) hW
    · simp only [circleSingleComponentField_iteratedDeriv, if_neg hi, abs_zero,
        mul_zero, E, ENNReal.toReal_zero, Real.sqrt_zero]
  have h := circleNorm_le_of_envelope
    (show (∑' i, E i) < ⊤ by rw [hE]; exact ENNReal.one_lt_top)
    hreg hM hH s (mul_nonneg hW hA) hb
  rw [hE, ENNReal.toReal_one, Real.sqrt_one, mul_one] at h
  have hnonneg : 0 ≤ (Fintype.card (CircleJetIndex s) : ℝ) * Real.pi :=
    mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le
  calc
    _ ≤ Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * (Real.pi * (W * A) ^ 2)) := h
    _ = Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) * Real.pi) * (W * A) := by
      rw [← mul_assoc, Real.sqrt_mul hnonneg, Real.sqrt_sq (mul_nonneg hW hA)]
    _ = _ := by dsimp only [W]; ring

end ContinuousFlexibility.Statements
