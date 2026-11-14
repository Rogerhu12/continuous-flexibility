module

public import ContinuousFlexibility.Radial.MorseTransitionBands

/-!
# Uniform suppression on every inner frequency band

These are the scalar estimates in `eq:inner-uniform-suppression` of
Section 6.  The threshold constant is chosen before the first cell index,
and the estimates hold for every action above the threshold, with no
upper bound on the frequency.  A second estimate treats a long positive
head, and also a central cut after its squared coordinate is used as the
length parameter.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real
open scoped Topology

/-- A logarithmic loss can use any prescribed positive fraction of the
exponential decay.  The additive constant is independent of `t`. -/
theorem inner_log_linear_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      a * log (1 + t) ≤ b * t + C := by
  let δ : ℝ := b / (a + 1)
  have hδ : 0 < δ := div_pos hb (by linarith)
  have hδeq : δ * (a + 1) = b := by
    exact div_mul_cancel₀ b (by linarith : a + 1 ≠ 0)
  refine ⟨a * (δ + |log δ| + 1), by positivity, ?_⟩
  intro t ht
  have ht1 : 0 < 1 + t := by linarith
  have hlog := log_le_sub_one_of_pos (mul_pos hδ ht1)
  rw [log_mul hδ.ne' ht1.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog ha
  have had : a * δ ≤ b := by nlinarith only [hδeq, hδ.le]
  have htime := mul_le_mul_of_nonneg_right had ht
  have hneglog := neg_le_abs (log δ)
  have hconst := mul_le_mul_of_nonneg_left hneglog ha
  nlinarith only [hmul, htime, hconst, ha]

/-- The logarithm of a cell error is bounded by a fixed constant minus
half its action.  This is uniform over all actions above `Cstar * q`. -/
theorem inner_suppression_exponent {c₁ c₂ c₃ Cstar : ℝ}
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃) (hCstar : 0 < Cstar)
    (hscale : 4 * c₁ / c₃ ≤ Cstar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q t : ℝ, 0 ≤ q → Cstar * q ≤ t →
      c₁ * q + c₂ * log (1 + t) - c₃ * t ≤ -(c₃ / 2) * t + C := by
  obtain ⟨C, hC, hlog⟩ := inner_log_linear_bound hc₂
    (by positivity : 0 < c₃ / 4)
  refine ⟨C, hC, ?_⟩
  intro q t hq ht
  have ht0 : 0 ≤ t := (mul_nonneg hCstar.le hq).trans ht
  have hlogt := hlog t ht0
  have hscale' : 4 * c₁ ≤ Cstar * c₃ := (div_le_iff₀ hc₃).mp hscale
  have hqscale := mul_le_mul_of_nonneg_right hscale' hq
  have htscale := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ c₃ / 4)
  nlinarith only [hlogt, hqscale, htscale]

/-- Once the positive action threshold is fixed, increasing the first
index makes every later cell error small simultaneously at every larger
frequency.  The tolerance is not an additional smallness hypothesis. -/
theorem inner_uniform_suppression_of_tendsto (q : ℕ → ℝ)
    (hq : Tendsto q atTop atTop) {c₁ c₂ c₃ Cstar : ℝ}
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃) (hCstar : 0 < Cstar)
    (hscale : 4 * c₁ / c₃ ≤ Cstar) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ t : ℝ, Cstar * q m ≤ t →
      exp (c₁ * q m + c₂ * log (1 + t) - c₃ * t) < η := by
  obtain ⟨C, _, hdecay⟩ := inner_suppression_exponent hc₂ hc₃ hCstar hscale
  let R : ℝ := (C - log η + 1) / ((c₃ / 2) * Cstar)
  have hden : 0 < (c₃ / 2) * Cstar := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq.eventually_ge_atTop (max 0 R))
  refine ⟨N, ?_⟩
  intro m hm t ht
  have hqm : 0 ≤ q m := (le_max_left 0 R).trans (hN m hm)
  have hRm : R ≤ q m := (le_max_right 0 R).trans (hN m hm)
  have hnum : C - log η + 1 ≤ q m * ((c₃ / 2) * Cstar) :=
    (div_le_iff₀ hden).mp hRm
  have htime := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ c₃ / 2)
  have hexp : c₁ * q m + c₂ * log (1 + t) - c₃ * t < log η := by
    have h := hdecay (q m) t hqm ht
    nlinarith only [h, hnum, htime]
  exact (exp_lt_exp.mpr hexp).trans_eq (exp_log hη)

/-- The order of choices is explicit: the threshold depends only on the
fixed exponents; the first index may then depend on the tolerance. -/
theorem exists_inner_uniform_suppression (q : ℕ → ℝ)
    (hq : Tendsto q atTop atTop) {c₁ c₂ c₃ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ 4 * c₁ / c₃ ≤ Cstar ∧
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        ∀ t : ℝ, Cstar * q m ≤ t →
          exp (c₁ * q m + c₂ * log (1 + t) - c₃ * t) < η := by
  have hCstar : 0 < 1 + 4 * c₁ / c₃ := by positivity
  have hscale : 4 * c₁ / c₃ ≤ 1 + 4 * c₁ / c₃ := by linarith
  refine ⟨1 + 4 * c₁ / c₃, hCstar, hscale, ?_⟩
  intro η hη
  exact inner_uniform_suppression_of_tendsto q hq hc₂ hc₃ hCstar hscale hη

/-- The actual coefficient exponent tends to infinity; a quadratic lower
bound already suffices for the inner suppression argument. -/
theorem inner_radialQ_tendsto : Tendsto Statements.radialQ atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 b)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : max 1 b ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hn1 : (1 : ℝ) ≤ n := (le_max_left 1 b).trans hcast
  have hbn : b ≤ (n : ℝ) := (le_max_right 1 b).trans hcast
  have hquadratic := mul_nonneg (sub_nonneg.mpr hn1) (Nat.cast_nonneg (α := ℝ) n)
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hquadratic]
  exact hbn.trans (hsq.trans (radial_nat_sq_le_Q n))

/-- Every cell strictly before the transition cell has sufficiently large
action.  The resulting tolerance is uniform in the transition index and
in the frequency, with no upper cutoff on either. -/
theorem inner_morse_uniform_suppression (T : Statements.MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {c₁ c₂ c₃ Cstar : ℝ} (hc₂ : 0 ≤ c₂) (hc₃ : 0 < c₃)
    (hCstar : 0 < Cstar) (hscale : 4 * c₁ / c₃ ≤ Cstar)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, T.index ≤ N ∧ ∀ m n j : ℕ, N ≤ m → m < n →
      Statements.radialFrequencyBand T Cstar n j →
      exp (c₁ * Statements.radialQ m +
        c₂ * log (1 + (j : ℝ) * sqrt (Statements.morseChainA T m)) -
        c₃ * ((j : ℝ) * sqrt (Statements.morseChainA T m))) < η := by
  obtain ⟨N, hN⟩ := inner_uniform_suppression_of_tendsto
    Statements.radialQ inner_radialQ_tendsto hc₂ hc₃ hCstar hscale hη
  refine ⟨max T.index N, le_max_left _ _, ?_⟩
  intro m n j hm hmn hband
  have hmIndex : T.index ≤ m := (le_max_left T.index N).trans hm
  exact hN m ((le_max_right T.index N).trans hm) _
    (morseTransition_earlier_cap_action T hCstar hd hband hmIndex hmn)

/-- Polynomial losses in both the frequency and a length parameter are
uniformly suppressed by the product of that frequency and length.  This
applies to cone heads directly, and to central cuts with `L = X₀²`. -/
theorem inner_product_uniform_suppression {A b d c η : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hc : 0 < c) (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ j : ℝ, 1 ≤ j →
      exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L) < η := by
  obtain ⟨C, _, hlog⟩ := inner_log_linear_bound (add_nonneg hb hd)
    (by positivity : 0 < c / 2)
  let R : ℝ := (A + C - log η + 1) / (c / 2)
  refine ⟨max 1 R, le_max_left _ _, ?_⟩
  intro L hL₀ j hj
  have hL : 1 ≤ L := (le_max_left 1 R).trans hL₀
  have hRL : R ≤ L := (le_max_right 1 R).trans hL₀
  have hnum : A + C - log η + 1 ≤ L * (c / 2) :=
    (div_le_iff₀ (by positivity : 0 < c / 2)).mp hRL
  have hj0 : 0 ≤ j := zero_le_one.trans hj
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hjt : j ≤ j * L := by
    nlinarith only [mul_nonneg hj0 (sub_nonneg.mpr hL)]
  have hLt : L ≤ j * L := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj) hL0]
  have ht : 0 ≤ j * L := mul_nonneg hj0 hL0
  have hjlog : log (1 + j) ≤ log (1 + j * L) :=
    log_le_log (by linarith) (by linarith only [hjt])
  have hLlog : log (1 + L) ≤ log (1 + j * L) :=
    log_le_log (by linarith) (by linarith only [hLt])
  have hbj := mul_le_mul_of_nonneg_left hjlog hb
  have hdL := mul_le_mul_of_nonneg_left hLlog hd
  have hdecay := hlog (j * L) ht
  have htime := mul_le_mul_of_nonneg_left hLt (by positivity : 0 ≤ c / 2)
  have hexp : A + b * log (1 + j) + d * log (1 + L) - c * j * L < log η := by
    nlinarith only [hbj, hdL, hdecay, htime, hnum]
  exact (exp_lt_exp.mpr hexp).trans_eq (exp_log hη)

end ContinuousFlexibility.Radial
