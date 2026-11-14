module

public import ContinuousFlexibility.Analysis.ScalarInverseScaleBounds
public import ContinuousFlexibility.Analysis.CircleCompositionTameBounds

/-!
# Interpolated positive jets of actual inverse circle lifts

The common high seminorm determines one positive dilation scale. A
forward derivative of order k costs at most k-1 powers of that scale;
conjugation by dilation gives exactly the same cost for the inverse.
The family index is arbitrary, so the constants are uniform on a fixed
low-seminorm neighborhood and across all circle labels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem rootScale_nat_pow {Q : ℝ} (hQ : 0 ≤ Q) (d : ℝ) (n : ℕ) :
    (Q ^ (1 / d)) ^ n = Q ^ ((n : ℝ) / d) := by
  rw [← Real.rpow_mul_natCast hQ]
  congr 1
  ring

section Interpolation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem interpolation_successor_le_rootScale
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (base loss high n : ℕ) (hbase : loss + 2 ≤ base)
    (hhigh : base < high) (hn : 1 ≤ n) (horder : n + 1 + loss < high)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        p b x ≤ C * (p base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (p c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (x : E) (Q : ℝ),
      p base x ≤ K → p high x ≤ Q → 1 ≤ Q →
      p (n + 1) x ≤ A * (Q ^ (1 / ((high : ℝ) - base))) ^ (n - 1) := by
  obtain ⟨A, hA, hb⟩ := interpolation_le_rpow_scale p hp base loss (n + 1) high
    hhigh (fun _ => horder) hinterp K hK
  refine ⟨A, hA, ?_⟩
  intro x Q hx hQx hQ
  have hd : 0 ≤ (high : ℝ) - base := sub_nonneg.mpr (by exact_mod_cast hhigh.le)
  have hc : (interpolationOrderCost base loss (n + 1) : ℝ) ≤ (n - 1 : ℕ) := by
    exact_mod_cast interpolationOrderCost_successor_le hbase hn
  have hpower : Q ^ ((interpolationOrderCost base loss (n + 1) : ℝ) /
      ((high : ℝ) - base)) ≤
      (Q ^ (1 / ((high : ℝ) - base))) ^ (n - 1) := by
    rw [rootScale_nat_pow (zero_le_one.trans hQ)]
    exact Real.rpow_le_rpow_of_exponent_le hQ (div_le_div_of_nonneg_right hc hd)
  exact (hb x Q hx hQx hQ).trans (mul_le_mul_of_nonneg_left hpower hA)

end Interpolation

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

/-- An actual inverse has scale cost k-1, uniformly over any collection
of charts lying in one low-seminorm ball. -/
theorem circleAffineLift_inverse_interpolated_jets
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ m, T.H (T.sample m) ^ γ ≤ A)
    (base loss high N : ℕ) (hbase : loss + 2 ≤ base) (hhigh : base < high)
    (horder : N + 1 + loss < high)
    (hinterp : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        S.grading b x ≤ C * (S.grading base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (S.grading c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} (e : ι → S.Space) (Q : ι → ℝ)
    (he : ∀ i, S.grading base (e i) ≤ K)
    (hQ : ∀ i, 1 ≤ Q i) (hQe : ∀ i, S.grading high (e i) ≤ Q i)
    (travel : ℕ → ℝ) (g : ι → ℕ → ℝ → ℝ)
    {a : ℝ} (ha : 0 < a)
    (hlower : ∀ i m θ, a ≤ deriv (circleAffineLift travel (S.decode (e i)) 1 m) θ)
    (hleft : ∀ i m θ, g i m (circleAffineLift travel (S.decode (e i)) 1 m θ) = θ)
    (hright : ∀ i m θ, circleAffineLift travel (S.decode (e i)) 1 m (g i m θ) = θ) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N → ∃ B : ℝ, 0 ≤ B ∧ ∀ i m θ,
      |iteratedDeriv n (g i m) θ| ≤
        B * Q i ^ (((n - 1 : ℕ) : ℝ) / ((high : ℝ) - base)) := by
  let f : (ι × ℕ) → ℝ → ℝ :=
    fun i => circleAffineLift travel (S.decode (e i.1)) 1 i.2
  let g' : (ι × ℕ) → ℝ → ℝ := fun i => g i.1 i.2
  let R : (ι × ℕ) → ℝ := fun i => Q i.1 ^ (1 / ((high : ℝ) - base))
  have hR (i : ι × ℕ) : 0 < R i :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le (hQ i.1)) _
  have hRone (i : ι × ℕ) : 1 ≤ R i := by
    have hd : 0 < (high : ℝ) - base := sub_pos.mpr (by exact_mod_cast hhigh)
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (hQ i.1) (one_div_nonneg.mpr hd.le)
  have hf (i : ι × ℕ) : ContDiff ℝ ∞ (f i) :=
    circleAffineLift_contDiff (fun m => ((hS.2.2.2.1 (e i.1)).1 m).1) travel 1 i.2
  have hfb (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i θ, |iteratedDeriv n (f i) θ| ≤ C * R i ^ (n - 1) := by
    obtain ⟨B, hB, hb⟩ := interpolation_successor_le_rootScale S.grading
      (gradedSeminorm_monotone (fun j => S.level j) S.bond)
      base loss high n hbase hhigh hn (by omega) hinterp K hK
    let P : ℝ := 2 * circleSobolevConstant * A
    have hP : 0 ≤ P := mul_nonneg
      (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hA
    refine ⟨1 + P * B, add_nonneg zero_le_one (mul_nonneg hP hB), ?_⟩
    intro i θ
    have hb' : S.grading (n + 1) (e i.1) ≤ B * R i ^ (n - 1) :=
      hb (e i.1) (Q i.1) (he i.1) (hQe i.1) (hQ i.1)
    have hpow : 1 ≤ R i ^ (n - 1) := one_le_pow₀ (hRone i)
    calc
      |iteratedDeriv n (f i) θ| ≤ 1 + P * S.grading (n + 1) (e i.1) :=
        circleAffineLift_jet_abs_le_exact_order (T := T) (γ := γ) (S := S)
          hS hH hA hHA travel (e i.1) i.2 n θ hn
      _ ≤ R i ^ (n - 1) + P * (B * R i ^ (n - 1)) :=
        add_le_add hpow (mul_le_mul_of_nonneg_left hb' hP)
      _ = (1 + P * B) * R i ^ (n - 1) := by ring
  have hg := inverse_iteratedDeriv_scale_bound_finite f g' R hR hf ha
    (fun i θ => hlower i.1 i.2 θ) (fun i θ => hleft i.1 i.2 θ)
    (fun i θ => hright i.1 i.2 θ) N hfb
  intro n hn hnN
  obtain ⟨B, hB, hb⟩ := hg n hn hnN
  refine ⟨B, hB, fun i m θ => ?_⟩
  have h := hb (i, m) θ
  simpa only [g', R, rootScale_nat_pow (zero_le_one.trans (hQ i))] using h

end ContinuousFlexibility.Statements
