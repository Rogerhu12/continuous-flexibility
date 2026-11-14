module

public import ContinuousFlexibility.Analysis.CircleInverseInterpolatedJets
public import ContinuousFlexibility.Analysis.CircleInverseFaaBounds

/-!
# Fixed-loss local growth of actual inverse composition

The inverse-jet scale budget is combined with the outer field's own
component energies. All finite terms are interpolated against one high
seminorm before a homogeneous linear-family estimate is extracted.
The loss is fixed before the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

theorem rootScale_mul_rpow_le {Q d : ℝ} (hQ : 1 ≤ Q) (hd : 0 < d)
    (n c : ℕ) (hcost : (n : ℝ) + c ≤ d) :
    (Q ^ (1 / d)) ^ n * Q ^ ((c : ℝ) / d) ≤ Q := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hexp : (n : ℝ) / d + (c : ℝ) / d ≤ 1 := by
    rw [← add_div, div_le_one hd]
    exact hcost
  calc
    _ = Q ^ ((n : ℝ) / d + (c : ℝ) / d) := by
      rw [rootScale_nat_pow hQpos.le, Real.rpow_add hQpos]
    _ ≤ Q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ hexp
    _ = Q := Real.rpow_one Q

theorem inverseCompositionTerm_cost_bound
    (base loss s : ℕ) (i : CircleCompositionTermIndex s) :
    (i.1.val 0).val - i.2.length +
        interpolationOrderCost base loss (circleCompositionTermOrder 0 i) ≤
      (s + (base + loss + 2)) - base := by
  have horder := i.1.property
  have hlength := i.2.length_le
  unfold circleCompositionTermOrder interpolationOrderCost
  split_ifs <;> omega

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- Uniform local growth for any actual inverse family. The family may
include both the chart parameter and the outer field, which supplies a
single constant on the whole low-seminorm polydisc. -/
theorem circleNorm_inverseCompose_family_growth
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 < T.M (T.sample m)) (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (base loss : ℕ) (hbase : loss + 2 ≤ base)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        S.grading b x ≤ C * (S.grading base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (S.grading c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} (e u : ι → S.Space)
    (he : ∀ i, S.grading base (e i) ≤ K)
    (hu : ∀ i, S.grading base (u i) ≤ K)
    (travel : ℕ → ℝ) (g : ι → ℕ → ℝ → ℝ)
    {a : ℝ} (ha : 0 < a)
    (hlower : ∀ i m θ, a ≤ deriv (circleAffineLift travel (S.decode (e i)) 1 m) θ)
    (hleft : ∀ i m θ, g i m (circleAffineLift travel (S.decode (e i)) 1 m θ) = θ)
    (hright : ∀ i m θ, circleAffineLift travel (S.decode (e i)) 1 m (g i m θ) = θ)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      circleNorm T γ s (fun m => S.decode (u i) m ∘ g i m) ≤
        C * (1 + S.grading (s + (base + loss + 2)) (e i) +
          S.grading (s + (base + loss + 2)) (u i)) := by
  classical
  let high : ℕ := s + (base + loss + 2)
  let Q (i : ι) : ℝ := 1 + S.grading high (e i) + S.grading high (u i)
  let R (i : ι) : ℝ := Q i ^ (1 / ((high : ℝ) - base))
  have hhigh : base < high := by dsimp [high]; omega
  have hd : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
  have hQ (i : ι) : 1 ≤ Q i := by
    dsimp [Q]
    linarith [apply_nonneg (S.grading high) (e i), apply_nonneg (S.grading high) (u i)]
  have hQe (i : ι) : S.grading high (e i) ≤ Q i := by
    dsimp [Q]
    linarith [apply_nonneg (S.grading high) (u i)]
  have hQu (i : ι) : S.grading high (u i) ≤ Q i := by
    dsimp [Q]
    linarith [apply_nonneg (S.grading high) (e i)]
  have hgb := circleAffineLift_inverse_interpolated_jets hS hH hA hHA
    base loss high s hbase hhigh (by dsimp [high]; omega) hinterp K hK
    e Q he hQ hQe travel g ha hlower hleft hright
  have hfinite (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ i m θ,
      1 ≤ n → n ≤ s → |iteratedDeriv n (g i m) θ| ≤ B * R i ^ (n - 1) := by
    by_cases hn : 1 ≤ n ∧ n ≤ s
    · obtain ⟨B, hB, hb⟩ := hgb n hn.1 hn.2
      refine ⟨B, hB, fun i m θ _ _ => ?_⟩
      simpa only [R, rootScale_nat_pow (zero_le_one.trans (hQ i))] using hb i m θ
    · exact ⟨0, le_rfl, fun _ _ _ h₁ h₂ => False.elim (hn ⟨h₁, h₂⟩)⟩
  choose B hB hb using hfinite
  have hg (i : ι) (m : ℕ) : ContDiff ℝ ∞ (g i m) :=
    returnChart_inverse_contDiff
      (circleAffineLift travel (S.decode (e i)) 1 m) (g i m)
      (circleAffineLift_contDiff (fun j => ((hS.2.2.2.1 (e i)).1 j).1) travel 1 m)
      (fun θ => ha.trans_le (hlower i m θ)) (hleft i m) (hright i m)
  have hterm (j : CircleCompositionTermIndex s) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
        (circleInversePartitionCoefficient B j.2 *
          R i ^ ((j.1.val 0).val - j.2.length)) *
            circleNorm T γ (circleCompositionTermOrder 0 j) (S.decode (u i)) ≤ C * Q i := by
    let order : ℕ := circleCompositionTermOrder 0 j
    have ho : order ≤ s + 1 := by
      have hj := j.1.property
      have hl := j.2.length_le
      dsimp [order, circleCompositionTermOrder]
      omega
    obtain ⟨C, hC, hc⟩ := interpolation_le_rpow_scale S.grading
      (gradedSeminorm_monotone (fun k => S.level k) S.bond)
      base loss order high hhigh (fun _ => by dsimp [high]; omega) hinterp K hK
    let P : ℝ := circleInversePartitionCoefficient B j.2
    have hP : 0 ≤ P := circleInversePartitionCoefficient_nonneg hB j.2
    refine ⟨P * C, mul_nonneg hP hC, ?_⟩
    intro i
    have hn : circleNorm T γ order (S.decode (u i)) ≤ S.grading order (u i) :=
      ((circleGrading_le_iff_circleNorm hS order (u i) (apply_nonneg _ _)).mp
        (le_refl (S.grading order (u i)))) order le_rfl
    have hout : circleNorm T γ order (S.decode (u i)) ≤
        C * Q i ^ ((interpolationOrderCost base loss order : ℝ) / ((high : ℝ) - base)) :=
      hn.trans (hc (u i) (Q i) (hu i) (hQu i) (hQ i))
    have hcostNat := inverseCompositionTerm_cost_bound base loss s j
    have hcost : (((j.1.val 0).val - j.2.length : ℕ) : ℝ) +
        (interpolationOrderCost base loss order : ℝ) ≤ (high : ℝ) - base := by
      have h : (((j.1.val 0).val - j.2.length : ℕ) : ℝ) +
          (interpolationOrderCost base loss order : ℝ) ≤ ((high - base : ℕ) : ℝ) := by
        exact_mod_cast hcostNat
      simpa only [Nat.cast_sub hhigh.le] using h
    have hscale := rootScale_mul_rpow_le (hQ i) hd
      ((j.1.val 0).val - j.2.length) (interpolationOrderCost base loss order) hcost
    have hR : 0 ≤ R i := Real.rpow_nonneg (zero_le_one.trans (hQ i)) _
    calc
      _ ≤ (P * R i ^ ((j.1.val 0).val - j.2.length)) *
          (C * Q i ^ ((interpolationOrderCost base loss order : ℝ) / ((high : ℝ) - base))) :=
        mul_le_mul_of_nonneg_left hout (mul_nonneg hP (pow_nonneg hR _))
      _ = (P * C) * (R i ^ ((j.1.val 0).val - j.2.length) *
          Q i ^ ((interpolationOrderCost base loss order : ℝ) / ((high : ℝ) - base))) := by ring
      _ ≤ (P * C) * Q i := mul_le_mul_of_nonneg_left hscale (mul_nonneg hP hC)
  choose C hC hc using hterm
  let prefactor : ℝ := Real.sqrt ((Fintype.card (CircleJetIndex s) : ℝ) *
    (Real.pi * (Fintype.card (CircleCompositionTermIndex s) : ℝ) ^ 2))
  refine ⟨prefactor * ∑ j, C j,
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun j _ => hC j)), ?_⟩
  intro i
  have hR : 0 ≤ R i := Real.rpow_nonneg (zero_le_one.trans (hQ i)) _
  have hnorm := circleNorm_comp_le_scaled_partitions (hS.2.2.2.1 (u i)) (hg i)
    (fun m => (hM m).le) (fun m => (hH m).le) B hB hR s
    (fun m n θ hn hns => hb n i m θ hn hns)
  have hsum : (∑ j : CircleCompositionTermIndex s,
      (circleInversePartitionCoefficient B j.2 * R i ^ ((j.1.val 0).val - j.2.length)) *
        circleNorm T γ (circleCompositionTermOrder 0 j) (S.decode (u i))) ≤
      (∑ j, C j) * Q i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => hc j i)
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)).trans_eq
    (mul_assoc prefactor (∑ j, C j) (Q i)).symm)

end ContinuousFlexibility.Statements
