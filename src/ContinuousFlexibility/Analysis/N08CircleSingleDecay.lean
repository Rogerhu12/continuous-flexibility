import ContinuousFlexibility.Analysis.N08CircleSingle

/-!
# Arbitrary envelope decay from one retained circle

Increasing the material exponent of each angular jet embeds the order
`s` energy into the order `s + N` energy. Retaining one label therefore
gains the exact factor `M_m ^ (-N)` in every actual projective grading.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def n08CircleJetWeightShift (s N : ℕ) : CircleJetIndex s ↪ CircleJetIndex (s + N) where
  toFun j := ⟨fun i => ⟨(j.val i).val + if i = 1 then N else 0, by
    have hi := (j.val i).isLt
    split_ifs <;> omega⟩, by
      have hj := j.property
      change (j.val 0).val + (if (0 : Fin 2) = 1 then N else 0) +
        ((j.val 1).val + (if (1 : Fin 2) = 1 then N else 0)) ≤ s + N
      simp only [show (0 : Fin 2) ≠ 1 by decide, if_false, if_true, Nat.add_zero]
      omega⟩
  inj' := by
    intro j k hjk
    apply Subtype.ext
    funext i
    apply Fin.ext
    have h := congrArg (fun z : CircleJetIndex (s + N) => (z.val i).val) hjk
    change (j.val i).val + (if i = 1 then N else 0) =
      (k.val i).val + (if i = 1 then N else 0) at h
    omega

theorem n08CircleJetWeightShift_angular (s N : ℕ) (j : CircleJetIndex s) :
    ((n08CircleJetWeightShift s N j).val 0).val = (j.val 0).val := by
  simp only [n08CircleJetWeightShift, zero_ne_one, if_false, Nat.add_zero]

theorem n08CircleJetWeightShift_weight (s N : ℕ) (j : CircleJetIndex s) :
    ((n08CircleJetWeightShift s N j).val 1).val = (j.val 1).val + N := by
  simp only [n08CircleJetWeightShift, if_true]

theorem n08CircleEnergyTerm_weight_shift (T : MaterialData) (γ : ℝ)
    (u : ℕ → ℝ → ℝ) (m s N : ℕ) (j : CircleJetIndex s) :
    ENNReal.ofReal ((T.M (T.sample m) ^ N) ^ 2) * n08CircleEnergyTerm T γ u m j =
      n08CircleEnergyTerm T γ u m (n08CircleJetWeightShift s N j) := by
  have hmul : (T.M (T.sample m) ^ N) ^ 2 *
      ((T.M (T.sample m) ^ (j.val 1).val * T.H (T.sample m) ^ (-γ)) ^ 2) =
      (T.M (T.sample m) ^ ((j.val 1).val + N) * T.H (T.sample m) ^ (-γ)) ^ 2 := by
    rw [pow_add]
    ring
  simp only [n08CircleEnergyTerm, n08CircleJetWeightShift_angular,
    n08CircleJetWeightShift_weight]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), hmul]

theorem n08CircleSingleField_scaled_energy_le (T : MaterialData) (γ : ℝ)
    (u : ℕ → ℝ → ℝ) (m s N : ℕ) :
    ENNReal.ofReal ((T.M (T.sample m) ^ N) ^ 2) *
      (∑' n, ∑ j : CircleJetIndex s,
        n08CircleEnergyTerm T γ (n08CircleSingleField m u) n j) ≤
      ∑' n, ∑ j : CircleJetIndex (s + N), n08CircleEnergyTerm T γ u n j := by
  rw [n08CircleSingleField_energy, Finset.mul_sum]
  calc
    _ = ∑ j : CircleJetIndex s,
        n08CircleEnergyTerm T γ u m (n08CircleJetWeightShift s N j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact n08CircleEnergyTerm_weight_shift T γ u m s N j
    _ = ∑ j ∈ Finset.univ.map (n08CircleJetWeightShift s N),
        n08CircleEnergyTerm T γ u m j := by rw [Finset.sum_map]
    _ ≤ ∑ j : CircleJetIndex (s + N), n08CircleEnergyTerm T γ u m j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => zero_le)
    _ ≤ _ := ENNReal.le_tsum (f := fun n => ∑ j : CircleJetIndex (s + N),
      n08CircleEnergyTerm T γ u n j) m

theorem n08CircleSingleField_circleNorm_decay {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) (m s N : ℕ)
    (hM : 0 < T.M (T.sample m)) :
    circleNorm T γ s (n08CircleSingleField m u) ≤
      (T.M (T.sample m) ^ N)⁻¹ * circleNorm T γ (s + N) u := by
  have he := n08CircleSingleField_scaled_energy_le T γ u m s N
  have hr := ENNReal.toReal_mono (hu.2.2 (s + N)).ne he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  have hsq : (T.M (T.sample m) ^ N * circleNorm T γ s (n08CircleSingleField m u)) ^ 2 ≤
      (circleNorm T γ (s + N) u) ^ 2 := by
    simpa only [mul_pow, circleNorm, Real.sq_sqrt ENNReal.toReal_nonneg,
      n08CircleEnergyTerm] using hr
  have hscaled := (sq_le_sq₀
    (mul_nonneg (pow_nonneg hM.le _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp hsq
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos hM _)).mpr (by simpa only [mul_comm] using hscaled)

/-- The decay is in the prescribed projective grading, not an auxiliary
sequence norm. Its constant is one and its extra order is exactly `N`. -/
theorem n08CircleSingle_grading_decay
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m s N : ℕ) (u : S.Space)
    (hM : 0 < T.M (T.sample m)) :
    S.grading s (n08CircleSingle hS m u) ≤
      (T.M (T.sample m) ^ N)⁻¹ * S.grading (s + N) u := by
  have hnonneg : 0 ≤ (T.M (T.sample m) ^ N)⁻¹ := inv_nonneg.mpr (pow_nonneg hM.le _)
  apply (gradedSeminorm_le_iff (fun s => S.level s) S.bond s _
    (mul_nonneg hnonneg (apply_nonneg _ _))).mpr
  intro i hi
  rw [hS.2.2.2.2.2.2.2, n08CircleSingle_decode]
  exact (n08CircleSingleField_circleNorm_decay (hS.2.2.2.1 u) m i N hM).trans
    (mul_le_mul_of_nonneg_left
      ((hS.2.2.2.2.2.2.2 u (i + N)).symm.trans_le
        (norm_coordinate_le_graded _ _ (Nat.add_le_add_right hi N) u)) hnonneg)

end ContinuousFlexibility.Statements
