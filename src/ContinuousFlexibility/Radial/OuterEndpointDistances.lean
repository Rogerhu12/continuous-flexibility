module

public import ContinuousFlexibility.Radial.OuterDeepFactory
public import ContinuousFlexibility.Radial.MorseTransitionBands

/-!
# Actual outer entrance distances at a moving cutoff

The realized partition bounds each seam's distance to the nearest endpoint.
The seam limits select the corresponding endpoint eventually. The left
entrance adds one genuine join of order `A_n^12`; this still has the size
of the next Morse scale `A_(n+1)`. No frequency is fixed in these estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

theorem morseRealized_seam_distance {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) (n : ℕ) (hn : M.index ≤ n) :
    min (morseChainSeam M right n - D.a) (D.b - morseChainSeam M right n) ≤
      C 0 * exp (-(n : ℝ) ^ 2) := by
  have hcover : ∀ side k, M.index ≤ k → ∀ r ∈ morseChainBlock M side k,
      ∃ m, D.cellIndex m = k ∧ r ∈ D.cells m := by
    rcases h with ⟨_, _, _, _, _, _, _, _, hc, _⟩
    exact hc
  obtain ⟨m, hm, hmem⟩ := hcover right n hn (morseChainSeam M right n)
    (left_mem_uIcc : morseChainSeam M right n ∈ morseChainBlock M right n)
  rcases h.accumulating with ⟨_, _, _, _, _, _, hdist, _⟩
  simpa only [hm] using (hdist m _ hmem).2

theorem morseRealized_seam_tendsto {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) :
    Tendsto (morseChainSeam M right) atTop (𝓝 (if right then D.b else D.a)) := by
  rcases h with ⟨_, _, _, _, _, _, hlim, _, _, _⟩
  cases right
  · change Tendsto (fun n => M.radius false n (M.rightX false n)) atTop (𝓝 D.a)
    simpa only [Bool.false_eq_true, ite_false] using (hlim false).2
  · change Tendsto (fun n => M.radius true n (M.leftX true n)) atTop (𝓝 D.b)
    simpa only [ite_true] using (hlim true).1

/-- The nearest endpoint at a sufficiently far seam is its own endpoint. -/
theorem morseRealized_eventually_seam_distance {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C)
    (right : Bool) :
    ∀ᶠ n : ℕ in atTop,
      (if right then D.b - morseChainSeam M right n
        else morseChainSeam M right n - D.a) ≤ C 0 * exp (-(n : ℝ) ^ 2) := by
  have hab := h.geometry.2.1
  have ht := morseRealized_seam_tendsto h right
  cases right with
  | false =>
      have hmid : D.a < (D.a + D.b) / 2 := by linarith
      filter_upwards [eventually_ge_atTop M.index,
        ht.eventually (Iio_mem_nhds hmid)] with n hn hside
      have hd := morseRealized_seam_distance h false n hn
      have hs : morseChainSeam M false n < (D.a + D.b) / 2 := hside
      rw [min_eq_left (by linarith : morseChainSeam M false n - D.a ≤
        D.b - morseChainSeam M false n)] at hd
      exact hd
  | true =>
      have hmid : (D.a + D.b) / 2 < D.b := by linarith
      filter_upwards [eventually_ge_atTop M.index,
        ht.eventually (Ioi_mem_nhds hmid)] with n hn hside
      have hd := morseRealized_seam_distance h true n hn
      have hs : (D.a + D.b) / 2 < morseChainSeam M true n := hside
      rw [min_eq_right (by linarith : D.b - morseChainSeam M true n ≤
        morseChainSeam M true n - D.a)] at hd
      exact hd

/-- The twelfth-power glue width is smaller than the next Gaussian scale. -/
theorem morseChainA_pow_twelve_le_next_exp (M : MorseChainData) {n : ℕ}
    (hn : 1 ≤ n) (hd : M.d n = morseChainInteger n) :
    morseChainA M n ^ 12 ≤ (9 : ℝ) ^ 12 * exp (-((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hb := morseChainA_exp_bounds M n hd
  have hA : 0 ≤ morseChainA M n := (by positivity : 0 ≤ exp (-(n : ℝ) ^ 2) / 3).trans hb.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    morseChainA M n ^ 12 ≤ (9 * exp (-(n : ℝ) ^ 2)) ^ 12 :=
      pow_le_pow_left₀ hA hb.2 12
    _ = (9 : ℝ) ^ 12 * exp (-12 * (n : ℝ) ^ 2) := by
      rw [mul_pow, ← exp_nat_mul]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply exp_le_exp.mpr
      push_cast
      nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- Both actual deep entrances have the size of the next retained scale.
The fixed factor also accounts for the left initial resistance join. -/
theorem morseOuterDeepEntrance_eventually_distance_le {M : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization M σ D C) :
    ∀ᶠ n : ℕ in atTop, ∀ right : Bool,
      (if right then D.b - morseOuterDeepEntrance M right n
        else morseOuterDeepEntrance M right n - D.a) ≤
        (3 * C 0 * (1 + (9 : ℝ) ^ 12)) * morseChainA M (n + 1) := by
  have hseam : ∀ᶠ n : ℕ in atTop, ∀ right : Bool,
      (if right then D.b - morseChainSeam M right (n + 1)
        else morseChainSeam M right (n + 1) - D.a) ≤
        C 0 * exp (-((n + 1 : ℕ) : ℝ) ^ 2) := by
    apply eventually_all.mpr
    intro right
    exact (tendsto_add_atTop_nat 1).eventually (morseRealized_eventually_seam_distance h right)
  filter_upwards [hseam, eventually_ge_atTop M.index, eventually_ge_atTop (1 : ℕ)]
    with n hs hn hn1
  intro right
  have hC := (h.constants_pos 0).le
  have hA := morseChainA_exp_bounds M (n + 1) (h.d_eq (n + 1) (hn.trans (Nat.le_succ n)))
  have hexp : exp (-((n + 1 : ℕ) : ℝ) ^ 2) ≤ 3 * morseChainA M (n + 1) := by
    linarith only [hA.1]
  have hglue := morseChainA_pow_twelve_le_next_exp M hn1 (h.d_eq n hn)
  have hentry :
      (if right then D.b - morseOuterDeepEntrance M right n
        else morseOuterDeepEntrance M right n - D.a) ≤
        C 0 * (1 + (9 : ℝ) ^ 12) * exp (-((n + 1 : ℕ) : ℝ) ^ 2) := by
    cases right with
    | true =>
        have he : morseOuterDeepEntrance M true n = morseChainSeam M true (n + 1) := by
          simpa only [morseOuterDeepEntrance, morseChainSeam, ite_true] using
            (h.join_data true n hn).2.2.1
        simp only [ite_true, he]
        apply (hs true).trans
        have hp : 0 ≤ C 0 * (9 : ℝ) ^ 12 * exp (-((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
        nlinarith only [hp]
    | false =>
        have hj := h.join_data false n hn
        have hwidth : morseOuterDeepEntrance M false n - morseChainSeam M false (n + 1) ≤
            C 0 * morseChainA M n ^ 12 := by
          simpa only [morseOuterDeepEntrance, morseChainSeam, hj.2.1, hj.2.2.1,
            Bool.false_eq_true, ite_false] using hj.2.2.2.1
        have hbound := mul_le_mul_of_nonneg_left hglue hC
        have hsL := hs false
        simp only [Bool.false_eq_true, ite_false] at hsL ⊢
        nlinarith only [hwidth, hbound, hsL]
  calc
    _ ≤ C 0 * (1 + (9 : ℝ) ^ 12) * exp (-((n + 1 : ℕ) : ℝ) ^ 2) := hentry
    _ ≤ C 0 * (1 + (9 : ℝ) ^ 12) * (3 * morseChainA M (n + 1)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end ContinuousFlexibility.Radial
