import ContinuousFlexibility.Analysis.SolveCircleProjection

/-!
# Retaining one actual circle component

The component projection is realized through the exact circle decoder.
It contracts every prescribed circle norm, and hence every projective
grading. No identification of a control interval with its label is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

def n08CircleSingleField (m : ℕ) (u : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun n => if n = m then u n else 0

theorem n08CircleSingleField_self (m : ℕ) (u : ℕ → ℝ → ℝ) :
    n08CircleSingleField m u m = u m := if_pos rfl

theorem n08CircleSingleField_ne {m n : ℕ} (u : ℕ → ℝ → ℝ) (hn : n ≠ m) :
    n08CircleSingleField m u n = 0 := if_neg hn

private theorem n08_iteratedDeriv_zero (s : ℕ) :
    iteratedDeriv s (0 : ℝ → ℝ) = 0 :=
  funext fun _ => iteratedDeriv_const_zero

def n08CircleEnergyTerm (T : MaterialData) (γ : ℝ) (u : ℕ → ℝ → ℝ)
    (m : ℕ) {s : ℕ} (j : CircleJetIndex s) : ℝ≥0∞ :=
  ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
    T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2

theorem n08CircleSingleField_energy (T : MaterialData) (γ : ℝ)
    (u : ℕ → ℝ → ℝ) (m s : ℕ) :
    (∑' n : ℕ, ∑ j : CircleJetIndex s,
      n08CircleEnergyTerm T γ (n08CircleSingleField m u) n j) =
        ∑ j : CircleJetIndex s, n08CircleEnergyTerm T γ u m j := by
  rw [tsum_eq_single m]
  · simp only [n08CircleEnergyTerm, n08CircleSingleField_self]
  · intro n hn
    simp only [n08CircleEnergyTerm, n08CircleSingleField_ne u hn,
      n08_iteratedDeriv_zero, eLpNorm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]

theorem n08CircleSingleField_mem {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) (m : ℕ) :
    CircleMember T γ (n08CircleSingleField m u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    by_cases hn : n = m
    · simpa only [n08CircleSingleField, if_pos hn] using hu.1 n
    · rw [n08CircleSingleField_ne u hn]
      exact ⟨contDiff_const, fun _ => rfl⟩
  · intro n b
    by_cases hn : n = m
    · simpa only [n08CircleSingleField, if_pos hn] using hu.2.1 n b
    · rw [n08CircleSingleField_ne u hn, n08_iteratedDeriv_zero]
      exact MemLp.zero
  · intro s
    change (∑' n, ∑ j : CircleJetIndex s,
      n08CircleEnergyTerm T γ (n08CircleSingleField m u) n j) < ⊤
    rw [n08CircleSingleField_energy]
    exact (ENNReal.le_tsum (f := fun n => ∑ j : CircleJetIndex s,
      n08CircleEnergyTerm T γ u n j) m).trans_lt (hu.2.2 s)

theorem n08CircleSingleField_circleNorm_le {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) (m s : ℕ) :
    circleNorm T γ s (n08CircleSingleField m u) ≤ circleNorm T γ s u := by
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono (hu.2.2 s).ne
  change (∑' n, ∑ j : CircleJetIndex s,
    n08CircleEnergyTerm T γ (n08CircleSingleField m u) n j) ≤ _
  rw [n08CircleSingleField_energy]
  exact ENNReal.le_tsum (f := fun n => ∑ j : CircleJetIndex s,
    n08CircleEnergyTerm T γ u n j) m

private def n08CircleSingleValue {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) (u : S.Space) : S.Space :=
  (hS.2.2.2.2.1 (n08CircleSingleField m (S.decode u))
    (n08CircleSingleField_mem (hS.2.2.2.1 u) m)).choose

private theorem n08CircleSingleValue_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) (u : S.Space) :
    S.decode (n08CircleSingleValue hS m u) = n08CircleSingleField m (S.decode u) :=
  (hS.2.2.2.2.1 (n08CircleSingleField m (S.decode u))
    (n08CircleSingleField_mem (hS.2.2.2.1 u) m)).choose_spec

def n08CircleSingleLinear {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) : S.Space →ₗ[ℝ] S.Space where
  toFun := n08CircleSingleValue hS m
  map_add' := by
    intro u v
    apply hS.2.2.2.2.2.1
    simp only [n08CircleSingleValue_decode, map_add]
    funext n θ
    by_cases hn : n = m <;> simp [n08CircleSingleField, hn]
  map_smul' := by
    intro a u
    apply hS.2.2.2.2.2.1
    simp only [n08CircleSingleValue_decode, map_smul]
    funext n θ
    by_cases hn : n = m <;> simp [n08CircleSingleField, hn]

theorem n08CircleSingleLinear_decode
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) (u : S.Space) :
    S.decode (n08CircleSingleLinear hS m u) = n08CircleSingleField m (S.decode u) :=
  n08CircleSingleValue_decode hS m u

theorem n08CircleSingleLinear_grading_le
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m s : ℕ) (u : S.Space) :
    S.grading s (n08CircleSingleLinear hS m u) ≤ S.grading s u := by
  apply (gradedSeminorm_le_iff (fun s => S.level s) S.bond s _
    (apply_nonneg _ _)).mpr
  intro i hi
  rw [hS.2.2.2.2.2.2.2, n08CircleSingleLinear_decode]
  exact (n08CircleSingleField_circleNorm_le (hS.2.2.2.1 u) m i).trans
    ((hS.2.2.2.2.2.2.2 u i).symm.trans_le (norm_coordinate_le_graded _ _ hi u))

def n08CircleSingle {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) : S.Space →L[ℝ] S.Space where
  toLinearMap := n08CircleSingleLinear hS m
  cont := continuous_projectiveLimit_of_tame
    (fun s => S.level s) S.bond (fun s => S.level s) S.bond
    (n08CircleSingleLinear hS m)
    (show IsTameLinear S.grading S.grading (n08CircleSingleLinear hS m) 0 0 from by
      intro s _
      refine ⟨1, fun u => ?_⟩
      simpa only [Nat.add_zero, NNReal.coe_one, one_mul] using
        n08CircleSingleLinear_grading_le hS m s u)

theorem n08CircleSingle_decode {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m : ℕ) (u : S.Space) :
    S.decode (n08CircleSingle hS m u) = n08CircleSingleField m (S.decode u) :=
  n08CircleSingleLinear_decode hS m u

theorem n08CircleSingle_grading_le {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hS : IsCircleModel T γ S) (m s : ℕ) (u : S.Space) :
    S.grading s (n08CircleSingle hS m u) ≤ S.grading s u :=
  n08CircleSingleLinear_grading_le hS m s u

end ContinuousFlexibility.Statements
