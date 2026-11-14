module

public import ContinuousFlexibility.Radial.MorseChainRadiusPlacement

/-!
# Distances to the actual accumulation radii

The outward order uses r on the right and -r on the left. A full next
cell supplies the lower distance bound. The upper bound is the tail sum
of the actual cell and connector lengths.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped BigOperators Topology

private theorem morse_gaussian_shift_le (n k : ℕ) :
    exp (-((n + k : ℕ) : ℝ) ^ 2) ≤ exp (-(n : ℝ) ^ 2) * exp (-1) ^ k := by
  have he : exp (-1 : ℝ) ^ k = exp (-(k : ℝ)) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [he, ← exp_add]
  apply exp_le_exp.mpr
  push_cast
  have hk₀ : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk₂ : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    by_cases hz : k = 0
    · subst k
      simp
    have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    nlinarith only [mul_nonneg hk₀ (sub_nonneg.mpr hk₁)]
  nlinarith only [hk₂, mul_nonneg hn₀ hk₀]

/-- The sum of the actual outward Morse scales starting at n is at most
one uniform constant times the actual first scale of that tail. -/
theorem morseChainA_tail_control (T : Statements.MorseChainData) (N : ℕ)
    (hd : ∀ n, T.d (N + n) = morseChainInteger (N + n)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n,
      Summable (fun k => Statements.morseChainA T (N + (n + k))) ∧
      (∑' k, Statements.morseChainA T (N + (n + k))) ≤
        K * Statements.morseChainA T (N + n) := by
  let q := exp (-1)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (by norm_num)
  have hGeom : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_norm_lt_one hq
  let M := ∑' k : ℕ, q ^ k
  have hM : 0 ≤ M := tsum_nonneg (fun _ => pow_nonneg (exp_pos _).le _)
  refine ⟨27 * (M + 1), by positivity, ?_⟩
  intro n
  let A := Statements.morseChainA T
  have hSum : Summable (fun k => A (N + (n + k))) := by
    simpa only [Nat.add_assoc] using
      morseChainA_summable_shift T (N + n) (fun k => by simpa only [Nat.add_assoc] using hd (n + k))
  have h₀ : exp (-((N + n : ℕ) : ℝ) ^ 2) / 3 ≤ A (N + n) :=
    (morseChainA_exp_bounds T (N + n) (hd n)).1
  have hA : 0 < A (N + n) := (by positivity : 0 < exp (-((N + n : ℕ) : ℝ) ^ 2) / 3).trans_le h₀
  let E := exp (-((N + n : ℕ) : ℝ) ^ 2)
  have hpoint (k : ℕ) : A (N + (n + k)) ≤ (9 * E) * q ^ k := calc
    _ ≤ 9 * exp (-((N + (n + k) : ℕ) : ℝ) ^ 2) :=
      (morseChainA_exp_bounds T (N + (n + k)) (hd (n + k))).2
    _ ≤ 9 * (E * q ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Nat.add_assoc] using morse_gaussian_shift_le (N + n) k
    _ = _ := (mul_assoc _ _ _).symm
  refine ⟨hSum, ?_⟩
  calc
    _ ≤ ∑' k, (9 * E) * q ^ k := hSum.tsum_le_tsum hpoint (hGeom.mul_left _)
    _ = (9 * E) * M := tsum_mul_left
    _ ≤ (27 * A (N + n)) * M := by
      have hE : E / 3 ≤ A (N + n) := h₀
      exact mul_le_mul_of_nonneg_right (by linarith only [hE]) hM
    _ ≤ _ := by nlinarith only [hA]

private theorem outward_sum_increments (enter : ℕ → ℝ) (n k : ℕ) :
    (∑ j ∈ Finset.range k, (enter (n + j + 1) - enter (n + j))) =
      enter (n + k) - enter n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      change enter (n + k) - enter n + (enter (n + k + 1) - enter (n + k)) =
        enter (n + k + 1) - enter n
      ring

/-- Distance bounds on a single outward ordering. They apply to the model
and its outward join, up through the next cell's entrance. -/
theorem morse_outward_distances {A enter leave : ℕ → ℝ} {endpoint cLo cHi K : ℝ}
    (hcHi : 0 ≤ cHi) (hT : Tendsto enter atTop (𝓝 endpoint))
    (horder : ∀ n, enter n < leave n ∧ leave n < enter (n + 1))
    (hwidth : ∀ n, cLo * A n ≤ leave n - enter n)
    (hstep : ∀ n, enter (n + 1) - enter n ≤ cHi * A n)
    (htail : ∀ n, Summable (fun k => A (n + k)) ∧ (∑' k, A (n + k)) ≤ K * A n)
    (hA : ∀ n, 0 ≤ A n) :
    ∀ n, ∀ x ∈ Icc (enter n) (enter (n + 1)),
      cLo * A (n + 1) ≤ endpoint - x ∧ endpoint - x ≤ cHi * K * A n := by
  have hmono : Monotone enter :=
    monotone_nat_of_le_succ (fun n => ((horder n).1.trans (horder n).2).le)
  have hTshift (n : ℕ) : Tendsto (fun k => enter (n + k)) atTop (𝓝 endpoint) := by
    have hshift : Tendsto (fun k : ℕ => n + k) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
    exact hT.comp hshift
  have hleave (n : ℕ) : leave n ≤ endpoint :=
    ge_of_tendsto' (hTshift (n + 1)) (fun k =>
      (horder n).2.le.trans (hmono (Nat.le_add_right (n + 1) k)))
  intro n x hx
  constructor
  · linarith only [hwidth (n + 1), hleave (n + 1), hx.2]
  · have hspan (k : ℕ) : enter (n + k) ≤ enter n + cHi * K * A n := by
      have h₁ : enter (n + k) - enter n ≤ cHi * (∑ j ∈ Finset.range k, A (n + j)) := by
        rw [← outward_sum_increments enter n k, Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => hstep (n + j)
      have h₂ : (∑ j ∈ Finset.range k, A (n + j)) ≤ K * A n :=
        ((htail n).1.sum_le_tsum _ (fun j _ => hA (n + j))).trans (htail n).2
      have h₃ := mul_le_mul_of_nonneg_left h₂ hcHi
      linarith only [h₁, h₃]
    have hEnd := le_of_tendsto' (hTshift n) hspan
    linarith only [hEnd, hx.1]

/-- For the same two physically placed chains, the outward block at n
has distance to its own accumulation radius between the next model
scale and a uniform multiple of the current model scale. -/
theorem morsePlaced_endpoint_distances
    (T : Statements.MorseChainData) (N : ℕ)
    (hd : ∀ n, T.d (N + n) = morseChainInteger (N + n))
    {A l u : ℕ → ℝ} {S : Bool → ℕ → ℝ}
    {c cLo cHi sLo sHi rLeft rRight : ℝ}
    (hAeq : ∀ n, A n = Statements.morseChainA T (N + n))
    (hA₁ : ∀ n, A n ≤ 1)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hsLo : 0 < sLo) (hS : ∀ side n, sLo ≤ S side n ∧ S side n ≤ sHi)
    (hl : ∀ n, 0 < l n) (hu : ∀ n, u n ≤ 2)
    (hwidth : ∀ n, cLo * A n ≤ u n - l n ∧ u n - l n ≤ cHi * A n)
    (hjoin : ∀ n, S true (n + 1) * l (n + 1) - S true n * u n =
        S true n * u n * morseChainJoinFraction A c n ∧
      S false n * l n - S false (n + 1) * u (n + 1) =
        S false (n + 1) * u (n + 1) * morseChainJoinFraction A c n)
    (hRight : Tendsto (fun n => S true n * l n) atTop (𝓝 rRight))
    (hLeft : Tendsto (fun n => S false n * u n) atTop (𝓝 rLeft)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n, ∀ x ∈ Icc (S true n * l n) (S true (n + 1) * l (n + 1)),
        sLo * cLo * A (n + 1) ≤ rRight - x ∧ rRight - x ≤ C * A n) ∧
      (∀ n, ∀ x ∈ Icc (S false (n + 1) * u (n + 1)) (S false n * u n),
        sLo * cLo * A (n + 1) ≤ x - rLeft ∧ x - rLeft ≤ C * A n) := by
  obtain ⟨K, hK, htail⟩ := morseChainA_tail_control T N hd
  have htail' (n : ℕ) : Summable (fun k => A (n + k)) ∧
      (∑' k, A (n + k)) ≤ K * A n := by
    simpa only [hAeq] using htail n
  have hA (n : ℕ) : 0 < A n := by
    rw [hAeq]
    have h := (morseChainA_exp_bounds T (N + n) (hd n)).1
    exact (by positivity : 0 < exp (-((N + n : ℕ) : ℝ) ^ 2) / 3).trans_le h
  have hSp (side : Bool) (n : ℕ) : 0 < S side n := hsLo.trans_le (hS side n).1
  have hsHi : 0 < sHi := (hSp true 0).trans_le (hS true 0).2
  have huL (n : ℕ) : l n < u n := sub_pos.mp
    ((mul_pos hcLo (hA n)).trans_le (hwidth n).1)
  have hup (n : ℕ) : 0 < u n := (hl n).trans (huL n)
  have hJ (n : ℕ) : 0 < morseChainJoinFraction A c n ∧
      morseChainJoinFraction A c n ≤ A n := by
    have hm : 0 < min (A n) (A (n + 1)) := lt_min (hA n) (hA (n + 1))
    refine ⟨mul_pos hc (pow_pos hm 12), ?_⟩
    calc
      morseChainJoinFraction A c n ≤ 1 * A n ^ 12 :=
        mul_le_mul hc₁ (pow_le_pow_left₀ hm.le (min_le_left _ _) 12) (by positivity) zero_le_one
      _ = A n * A n ^ 11 := by ring
      _ ≤ A n * 1 := mul_le_mul_of_nonneg_left
        (by simpa only [one_pow] using pow_le_pow_left₀ (hA n).le (hA₁ n) 11) (hA n).le
      _ = _ := mul_one _
  have hwidthLo (side : Bool) (n : ℕ) :
      sLo * cLo * A n ≤ S side n * (u n - l n) := calc
    _ = sLo * (cLo * A n) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul (hS side n).1 (hwidth n).1
      (mul_nonneg hcLo.le (hA n).le) (hSp side n).le
  have hwidthHi (side : Bool) (n : ℕ) :
      S side n * (u n - l n) ≤ sHi * (cHi * A n) :=
    mul_le_mul (hS side n).2 (hwidth n).2 (sub_nonneg.mpr (huL n).le) hsHi.le
  have hgapHi (side : Bool) (k n : ℕ) :
      S side k * u k * morseChainJoinFraction A c n ≤ (sHi * 2) * A n :=
    mul_le_mul (mul_le_mul (hS side k).2 (hu k) (hup k).le hsHi.le) (hJ n).2
      (hJ n).1.le (by positivity)
  let D := sHi * (cHi + 2)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hoR (n : ℕ) : S true n * l n < S true n * u n ∧
      S true n * u n < S true (n + 1) * l (n + 1) :=
    ⟨mul_lt_mul_of_pos_left (huL n) (hSp true n),
      sub_pos.mp ((hjoin n).1.symm ▸ mul_pos (mul_pos (hSp true n) (hup n)) (hJ n).1)⟩
  have hoL (n : ℕ) : -(S false n * u n) < -(S false n * l n) ∧
      -(S false n * l n) < -(S false (n + 1) * u (n + 1)) :=
    ⟨neg_lt_neg (mul_lt_mul_of_pos_left (huL n) (hSp false n)),
      neg_lt_neg (sub_pos.mp ((hjoin n).2.symm ▸
        mul_pos (mul_pos (hSp false (n + 1)) (hup (n + 1))) (hJ n).1))⟩
  have hstepR (n : ℕ) : S true (n + 1) * l (n + 1) - S true n * l n ≤ D * A n := by
    dsimp only [D]
    nlinarith only [(hjoin n).1, hwidthHi true n, hgapHi true n n]
  have hstepL (n : ℕ) : -(S false (n + 1) * u (n + 1)) - -(S false n * u n) ≤ D * A n := by
    dsimp only [D]
    nlinarith only [(hjoin n).2, hwidthHi false n, hgapHi false (n + 1) n]
  have hWL (n : ℕ) : sLo * cLo * A n ≤ -(S false n * l n) - -(S false n * u n) := by
    nlinarith only [hwidthLo false n]
  have hWR (n : ℕ) : sLo * cLo * A n ≤ S true n * u n - S true n * l n := by
    nlinarith only [hwidthLo true n]
  have hL := morse_outward_distances hD.le hLeft.neg hoL hWL hstepL htail' (fun n => (hA n).le)
  refine ⟨D * K, mul_pos hD hK, morse_outward_distances hD.le hRight hoR hWR hstepR htail'
    (fun n => (hA n).le), ?_⟩
  intro n x hx
  have hy : -x ∈ Icc (-(S false n * u n)) (-(S false (n + 1) * u (n + 1))) :=
    ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
  have h := hL n (-x) hy
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

end ContinuousFlexibility.Radial
