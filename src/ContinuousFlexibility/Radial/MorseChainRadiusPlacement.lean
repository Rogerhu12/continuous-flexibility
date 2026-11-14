module

public import ContinuousFlexibility.Radial.MorseChainParameters
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Radius placement for both accumulating Morse ends

The fraction of the preceding physical radius used for a connector is
c min(A_n,A_{n+1})^12. The two outward recursions have opposite orientations.
The logarithmic increments are absolutely summable, so normalizing the
left radius factor achieves a prescribed positive left endpoint.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Real Filter
open scoped BigOperators Topology

/-- The literal fraction of the initial physical radius occupied by a
positive connector between adjacent model cells. -/
noncomputable def morseChainJoinFraction (A : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  c * (min (A n) (A (n + 1))) ^ 12

noncomputable def morseChainRadiusStep (A l u : ℕ → ℝ) (c : ℝ) (right : Bool) (n : ℕ) : ℝ :=
  if right then log (u n) + log (1 + morseChainJoinFraction A c n) - log (l (n + 1))
  else log (l n) - log (u (n + 1)) - log (1 + morseChainJoinFraction A c n)

noncomputable def morseChainRadiusFactor (A l u : ℕ → ℝ) (c q : ℝ)
    (right : Bool) (n : ℕ) : ℝ :=
  q * exp (∑ k ∈ Finset.range n, morseChainRadiusStep A l u c right k)

private theorem exp_neg_nat_sq_summable (N : ℕ) :
    Summable (fun n : ℕ => exp (-((N + n : ℕ) : ℝ) ^ 2)) := by
  have hq : ‖exp (-1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun n => (exp_pos _).le) _ (summable_geometric_of_norm_lt_one hq)
  intro n
  rw [← exp_nat_mul]
  apply exp_le_exp.mpr
  have hNn : (n : ℝ) ≤ ((N + n : ℕ) : ℝ) := by exact_mod_cast (show n ≤ N + n by omega)
  by_cases hz : n = 0
  · subst n
    simp
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn₂ : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc
      (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hnr hn₀
      _ = _ := (pow_two _).symm
  have hsq := hn₂.trans (pow_le_pow_left₀ hn₀ hNn 2)
  nlinarith only [hsq]

/-- The actual manuscript coefficients, with the actual least nonsquare
choice, form a summable sequence starting at any index. -/
theorem morseChainA_summable_shift (T : Statements.MorseChainData) (N : ℕ)
    (hd : ∀ n, T.d (N + n) = morseChainInteger (N + n)) :
    Summable (fun n => Statements.morseChainA T (N + n)) :=
  Summable.of_nonneg_of_le
    (fun n => le_trans (by positivity) (morseChainA_exp_bounds T (N + n) (hd n)).1)
    (fun n => (morseChainA_exp_bounds T (N + n) (hd n)).2)
    ((exp_neg_nat_sq_summable N).mul_left 9)

private theorem morseChainJoinFraction_bounds {A : ℕ → ℝ} {c : ℝ}
    (hA : ∀ n, 0 < A n) (hA₁ : ∀ n, A n ≤ 1) (hc : 0 < c) (hc₁ : c ≤ 1) (n : ℕ) :
    0 < morseChainJoinFraction A c n ∧ morseChainJoinFraction A c n ≤ A n := by
  have hm : 0 < min (A n) (A (n + 1)) := lt_min (hA n) (hA (n + 1))
  refine ⟨mul_pos hc (pow_pos hm 12), ?_⟩
  calc
    morseChainJoinFraction A c n ≤ 1 * A n ^ 12 :=
      mul_le_mul hc₁ (pow_le_pow_left₀ hm.le (min_le_left _ _) 12) (by positivity) zero_le_one
    _ = A n * A n ^ 11 := by ring
    _ ≤ A n * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [one_pow] using pow_le_pow_left₀ (hA n).le (hA₁ n) 11) (hA n).le
    _ = _ := mul_one _

private theorem abs_log_le_two_mul_abs_sub_one {r : ℝ} (hr : (1 / 2 : ℝ) ≤ r) :
    |log r| ≤ 2 * |r - 1| := by
  have hp : 0 < r := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hr
  have hfrac : 1 - r⁻¹ = (r - 1) / r := by field_simp [hp.ne']
  have h := one_sub_inv_le_log_of_pos hp
  rw [hfrac] at h
  have hdiv : |(r - 1) / r| ≤ 2 * |r - 1| := by
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith only [mul_nonneg (abs_nonneg (r - 1)) (show 0 ≤ 2 * r - 1 by linarith only [hr])]
  have hlo := (abs_le.mp hdiv).1
  have hup := log_le_sub_one_of_pos hp
  have habs := le_abs_self (r - 1)
  exact abs_le.mpr ⟨hlo.trans h, by linarith only [hup, habs, abs_nonneg (r - 1)]⟩

private theorem morse_radius_end_ge_half {A l : ℕ → ℝ}
    (hA₀ : ∀ n, A n ≤ 1 / 1000) (hl : ∀ n, |l n - 1| ≤ 6 * A n) (n : ℕ) :
    (1 / 2 : ℝ) ≤ l n := by
  linarith only [(abs_le.mp (hl n)).1, hA₀ n]

private theorem morseChainRadiusStep_abs_summable {A l u : ℕ → ℝ} {c : ℝ}
    (hA : ∀ n, 0 < A n) (hA₀ : ∀ n, A n ≤ 1 / 1000) (hSum : Summable A)
    (hl : ∀ n, |l n - 1| ≤ 6 * A n) (hu : ∀ n, |u n - 1| ≤ 6 * A n)
    (hc : 0 < c) (hc₁ : c ≤ 1) (right : Bool) :
    Summable (fun n => |morseChainRadiusStep A l u c right n|) := by
  have hA₁ (n : ℕ) : A n ≤ 1 := (hA₀ n).trans (by norm_num)
  have hAs : Summable (fun n => A (n + 1)) := (summable_nat_add_iff 1).mpr hSum
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _
    ((hSum.mul_left 13).add (hAs.mul_left 12))
  intro n
  change |morseChainRadiusStep A l u c right n| ≤ 13 * A n + 12 * A (n + 1)
  have hL (k : ℕ) : |log (l k)| ≤ 12 * A k := by
    have h := abs_log_le_two_mul_abs_sub_one (morse_radius_end_ge_half hA₀ hl k)
    linarith only [h, hl k]
  have hU (k : ℕ) : |log (u k)| ≤ 12 * A k := by
    have h := abs_log_le_two_mul_abs_sub_one (morse_radius_end_ge_half hA₀ hu k)
    linarith only [h, hu k]
  let j := morseChainJoinFraction A c n
  have hj : 0 < j ∧ j ≤ A n := morseChainJoinFraction_bounds hA hA₁ hc hc₁ n
  have hp : 0 < 1 + j := by linarith only [hj.1]
  have hJ : |log (1 + j)| ≤ A n := by
    rw [abs_of_nonneg (log_nonneg (by linarith only [hj.1]))]
    linarith only [log_le_sub_one_of_pos hp, hj.2]
  cases right
  · change |log (l n) - log (u (n + 1)) - log (1 + j)| ≤ _
    calc
      _ ≤ |log (l n) - log (u (n + 1))| + |log (1 + j)| := abs_sub _ _
      _ ≤ (|log (l n)| + |log (u (n + 1))|) + |log (1 + j)| :=
        add_le_add_left (abs_sub _ _) _
      _ ≤ _ := by linarith only [hL n, hU (n + 1), hJ]
  · change |log (u n) + log (1 + j) - log (l (n + 1))| ≤ _
    calc
      _ ≤ |log (u n) + log (1 + j)| + |log (l (n + 1))| := abs_sub _ _
      _ ≤ (|log (u n)| + |log (1 + j)|) + |log (l (n + 1))| :=
        add_le_add_left (abs_add_le _ _) _
      _ ≤ _ := by linarith only [hU n, hL (n + 1), hJ]

private theorem morseChainRadiusFactor_succ {A l u : ℕ → ℝ} {c q : ℝ}
    (right : Bool) (n : ℕ) :
    morseChainRadiusFactor A l u c q right (n + 1) =
      morseChainRadiusFactor A l u c q right n * exp (morseChainRadiusStep A l u c right n) := by
  unfold morseChainRadiusFactor
  rw [Finset.sum_range_succ, exp_add, mul_assoc]

private theorem morse_radius_end_tendsto {A l : ℕ → ℝ} (hSum : Summable A)
    (hl : ∀ n, |l n - 1| ≤ 6 * A n) : Tendsto l atTop (𝓝 1) := by
  have hA := hSum.tendsto_atTop_zero
  have hU : Tendsto (fun n => 1 + (6 : ℝ) * A n) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := (6 : ℝ))).mul hA)
  have hL : Tendsto (fun n => 1 - (6 : ℝ) * A n) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_const_nhds (x := (6 : ℝ))).mul hA)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hL hU ?_ ?_
  · intro n
    exact (by
      have h := (abs_le.mp (hl n)).1
      linarith only [h] : 1 - 6 * A n ≤ l n)
  · intro n
    exact (by
      have h := (abs_le.mp (hl n)).2
      linarith only [h] : l n ≤ 1 + 6 * A n)

/-- There are uniformly positive and bounded dilation factors for both
orientations. The equations give the exact physical connector lengths;
the positive left accumulation radius can be prescribed independently
of the initial right dilation. -/
theorem exists_morseChainRadiusPlacement {A l u : ℕ → ℝ} {c rLeft qRight : ℝ}
    (hA : ∀ n, 0 < A n) (hA₀ : ∀ n, A n ≤ 1 / 1000) (hSum : Summable A)
    (hl : ∀ n, |l n - 1| ≤ 6 * A n) (hu : ∀ n, |u n - 1| ≤ 6 * A n)
    (hlu : ∀ n, l n < u n)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hrLeft : 0 < rLeft) (hqRight : 0 < qRight) :
    ∃ S : Bool → ℕ → ℝ, ∃ rRight Smin Smax : ℝ,
      0 < rRight ∧ 0 < Smin ∧ S true 0 = qRight ∧
      (∀ side n, Smin ≤ S side n ∧ S side n ≤ Smax) ∧
      (∀ n, S true (n + 1) * l (n + 1) - S true n * u n =
          S true n * u n * morseChainJoinFraction A c n ∧
        S false n * l n - S false (n + 1) * u (n + 1) =
          S false (n + 1) * u (n + 1) * morseChainJoinFraction A c n) ∧
      (∀ n, S true n * l n < S true n * u n ∧
        S true n * u n < S true (n + 1) * l (n + 1) ∧
        S false (n + 1) * u (n + 1) < S false n * l n ∧
        S false n * l n < S false n * u n) ∧
      (∀ side,
        Tendsto (fun n => S side n * l n) atTop (𝓝 (if side then rRight else rLeft)) ∧
        Tendsto (fun n => S side n * u n) atTop (𝓝 (if side then rRight else rLeft))) := by
  let step := morseChainRadiusStep A l u c
  have hsabs (side : Bool) : Summable (fun n => |step side n|) :=
    morseChainRadiusStep_abs_summable hA hA₀ hSum hl hu hc hc₁ side
  have hs (side : Bool) : Summable (step side) :=
    (show Summable (fun n => ‖step side n‖) by simpa only [Real.norm_eq_abs] using hsabs side).of_norm
  let U := (∑' n, |step false n|) + (∑' n, |step true n|)
  have hUL : 0 ≤ ∑' n, |step false n| := tsum_nonneg fun _ => abs_nonneg _
  have hUR : 0 ≤ ∑' n, |step true n| := tsum_nonneg fun _ => abs_nonneg _
  have hUpart (side : Bool) : ∑' n, |step side n| ≤ U := by
    cases side
    · exact le_add_of_nonneg_right hUR
    · exact le_add_of_nonneg_left hUL
  let qLeft := rLeft / exp (∑' n, step false n)
  have hqLeft : 0 < qLeft := div_pos hrLeft (exp_pos _)
  let q (side : Bool) : ℝ := if side then qRight else qLeft
  have hq (side : Bool) : 0 < q side := by cases side <;> assumption
  let S (side : Bool) := morseChainRadiusFactor A l u c (q side) side
  let rRight := qRight * exp (∑' n, step true n)
  let Smin := min qLeft qRight * exp (-U)
  let Smax := max qLeft qRight * exp U
  have hS (side : Bool) (n : ℕ) : 0 < S side n := mul_pos (hq side) (exp_pos _)
  have hrRight : 0 < rRight := mul_pos hqRight (exp_pos _)
  have hSmin : 0 < Smin := mul_pos (lt_min hqLeft hqRight) (exp_pos _)
  have hSc (side : Bool) (n : ℕ) : Smin ≤ S side n ∧ S side n ≤ Smax := by
    let P := ∑ k ∈ Finset.range n, step side k
    have hP : |P| ≤ U := calc
      _ ≤ ∑ k ∈ Finset.range n, |step side k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑' k, |step side k| := (hsabs side).sum_le_tsum _ (fun _ _ => abs_nonneg _)
      _ ≤ _ := hUpart side
    have hqL : min qLeft qRight ≤ q side := by
      cases side
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hqU : q side ≤ max qLeft qRight := by
      cases side
      · exact le_max_left _ _
      · exact le_max_right _ _
    change min qLeft qRight * exp (-U) ≤ q side * exp P ∧
      q side * exp P ≤ max qLeft qRight * exp U
    exact ⟨mul_le_mul hqL (exp_le_exp.mpr (abs_le.mp hP).1)
        (exp_pos _).le (hq side).le,
      mul_le_mul hqU (exp_le_exp.mpr (abs_le.mp hP).2)
        (exp_pos _).le ((hq side).le.trans hqU)⟩
  have hlp (n : ℕ) : 0 < l n := (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (morse_radius_end_ge_half hA₀ hl n)
  have hup (n : ℕ) : 0 < u n := (hlp n).trans (hlu n)
  have hj (n : ℕ) : 0 < morseChainJoinFraction A c n := (morseChainJoinFraction_bounds
    hA (fun k => (hA₀ k).trans (by norm_num)) hc hc₁ n).1
  have hjoinR (n : ℕ) : S true (n + 1) * l (n + 1) - S true n * u n =
      S true n * u n * morseChainJoinFraction A c n := by
    have hstep : S true (n + 1) = S true n * exp (step true n) :=
      morseChainRadiusFactor_succ true n
    have he : exp (step true n) = u n * (1 + morseChainJoinFraction A c n) / l (n + 1) := by
      change exp (log (u n) + log (1 + morseChainJoinFraction A c n) - log (l (n + 1))) = _
      rw [exp_sub, exp_add, exp_log (hup n), exp_log (by linarith only [hj n] : 0 < 1 + morseChainJoinFraction A c n),
        exp_log (hlp (n + 1))]
    rw [hstep, he]
    field_simp [(hlp (n + 1)).ne']
    ring
  have hjoinL (n : ℕ) : S false n * l n - S false (n + 1) * u (n + 1) =
      S false (n + 1) * u (n + 1) * morseChainJoinFraction A c n := by
    have hstep : S false (n + 1) = S false n * exp (step false n) :=
      morseChainRadiusFactor_succ false n
    have hp : 0 < 1 + morseChainJoinFraction A c n := by linarith only [hj n]
    have he : exp (step false n) = l n / u (n + 1) / (1 + morseChainJoinFraction A c n) := by
      change exp (log (l n) - log (u (n + 1)) - log (1 + morseChainJoinFraction A c n)) = _
      rw [exp_sub, exp_sub, exp_log (hlp n), exp_log (hup (n + 1)), exp_log hp]
    rw [hstep, he]
    field_simp [(hup (n + 1)).ne', hp.ne']
    ring
  have hlimit (side : Bool) : Tendsto (S side) atTop (𝓝 (if side then rRight else rLeft)) := by
    have hsum : Tendsto (fun n => ∑ k ∈ Finset.range n, step side k) atTop
        (𝓝 (∑' k, step side k)) := (hs side).hasSum.tendsto_sum_nat
    have h := (tendsto_const_nhds (x := q side)).mul (continuous_exp.continuousAt.tendsto.comp hsum)
    change Tendsto (S side) atTop (𝓝 (q side * exp (∑' k, step side k))) at h
    cases side
    · change Tendsto (S false) atTop (𝓝 rLeft)
      have he : q false * exp (∑' k, step false k) = rLeft := by
        change rLeft / exp (∑' k, step false k) * exp (∑' k, step false k) = rLeft
        exact div_mul_cancel₀ _ (exp_pos _).ne'
      rwa [he] at h
    · exact h
  refine ⟨S, rRight, Smin, Smax, hrRight, hSmin, ?_, hSc,
    fun n => ⟨hjoinR n, hjoinL n⟩, ?_, ?_⟩
  · change qRight * exp (∑ k ∈ Finset.range 0, step true k) = qRight
    simp
  · intro n
    refine ⟨mul_lt_mul_of_pos_left (hlu n) (hS true n), ?_, ?_,
      mul_lt_mul_of_pos_left (hlu n) (hS false n)⟩
    · have hpos : 0 < S true n * u n * morseChainJoinFraction A c n :=
        mul_pos (mul_pos (hS true n) (hup n)) (hj n)
      exact sub_pos.mp ((hjoinR n).symm ▸ hpos)
    · have hpos : 0 < S false (n + 1) * u (n + 1) * morseChainJoinFraction A c n :=
        mul_pos (mul_pos (hS false (n + 1)) (hup (n + 1))) (hj n)
      exact sub_pos.mp ((hjoinL n).symm ▸ hpos)
  · intro side
    exact ⟨by simpa only [mul_one] using (hlimit side).mul (morse_radius_end_tendsto hSum hl),
      by simpa only [mul_one] using (hlimit side).mul (morse_radius_end_tendsto hSum hu)⟩

end ContinuousFlexibility.Radial
