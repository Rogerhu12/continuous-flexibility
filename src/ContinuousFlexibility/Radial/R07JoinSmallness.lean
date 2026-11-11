import ContinuousFlexibility.Radial.HeightBandCount
import ContinuousFlexibility.Radial.HeightJoinTransfer

/-!
# Uniform smallness of the transfer across a preceding join

At band `n`, the frequency is bounded by `2 C q_n exp (n²/2)`.
The preceding join has length at most `K A_{n-1}^12`; its height
contrast is at most `exp (6 n²)` after the logarithmic contrast
estimate is applied. These coarse bounds already make its transfer
action `O(q_n² exp (-4 n²))`. In particular the action is uniformly
smaller than any fixed multiple of the required margin `exp (-n²)`.

The estimates here do not distinguish left and right. They use the
minimum radius of the interval and the absolute distance traversed,
as does `joinState_transfer`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology

/-- An envelope for the join-transfer action at a transition band. -/
def r07JoinEnvelope (K C rmin : ℝ) (n : ℕ) : ℝ :=
  (8 * (9 : ℝ) ^ 12 * K * C ^ 2 / rmin) *
    Statements.radialQ n ^ 2 * exp (-4 * (n : ℝ) ^ 2)

/-- A frequency bound in the form needed by the transfer system. -/
theorem r07_band_frequency_square_le (T : Statements.MorseChainData) {C : ℝ}
    (hC : 0 ≤ C) {n j : ℕ} (hd : T.d n = morseChainInteger n)
    (hband : Statements.radialFrequencyBand T C n j) :
    (j : ℝ) ^ 2 ≤ 4 * C ^ 2 * Statements.radialQ n ^ 2 * exp ((n : ℝ) ^ 2) := by
  have hj : (j : ℝ) ≤ 2 * C * Statements.radialQ n * exp ((n : ℝ) ^ 2 / 2) :=
    hband.2.2.le.trans (radialFrequencyThreshold_le_exp T hC n hd)
  have he : exp ((n : ℝ) ^ 2 / 2) ^ 2 = exp ((n : ℝ) ^ 2) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  calc
    _ ≤ (2 * C * Statements.radialQ n * exp ((n : ℝ) ^ 2 / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg j) hj 2
    _ = _ := by rw [mul_pow, he]; ring

/-- The twelfth power of the preceding cell scale absorbs the frequency
and the full height contrast. -/
theorem r07_join_action_le (T : Statements.MorseChainData) {C K rmin : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) (hrmin : 0 < rmin)
    (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n)
    {n j : ℕ} (hn : 24 ≤ n) (hprev : T.index < n)
    (hband : Statements.radialFrequencyBand T C n j)
    {contrast length : ℝ} (hcontrast₀ : 0 ≤ contrast)
    (hcontrast : contrast ≤ exp (6 * (n : ℝ) ^ 2))
    (hlength₀ : 0 ≤ length)
    (hlength : length ≤ K * Statements.morseChainA T (n - 1) ^ 12) :
    2 * (j : ℝ) ^ 2 * contrast / rmin * length ≤ r07JoinEnvelope K C rmin n := by
  have hnprev : T.index ≤ n - 1 := by omega
  have hAprev := morseChainA_exp_bounds T (n - 1) (hd (n - 1) hnprev)
  have hAprev₀ : 0 ≤ Statements.morseChainA T (n - 1) :=
    (by positivity : (0 : ℝ) ≤ exp (-((n - 1 : ℕ) : ℝ) ^ 2) / 3).trans hAprev.1
  have hp : Statements.morseChainA T (n - 1) ^ 12 ≤
      (9 : ℝ) ^ 12 * exp (-12 * ((n - 1 : ℕ) : ℝ) ^ 2) := by
    calc
      _ ≤ (9 * exp (-((n - 1 : ℕ) : ℝ) ^ 2)) ^ 12 :=
        pow_le_pow_left₀ hAprev₀ hAprev.2 12
      _ = _ := by
        rw [mul_pow, ← exp_nat_mul]
        congr 2
        norm_num <;> ring
  have hlength' : length ≤ K * (9 : ℝ) ^ 12 *
      exp (-12 * ((n - 1 : ℕ) : ℝ) ^ 2) := by
    calc
      _ ≤ K * Statements.morseChainA T (n - 1) ^ 12 := hlength
      _ ≤ K * ((9 : ℝ) ^ 12 * exp (-12 * ((n - 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hp hK
      _ = _ := by ring
  have hj := r07_band_frequency_square_le T hC.le (hd n hband.1) hband
  have hmain : 2 * (j : ℝ) ^ 2 * contrast / rmin * length ≤
      2 * (4 * C ^ 2 * Statements.radialQ n ^ 2 * exp ((n : ℝ) ^ 2)) *
        exp (6 * (n : ℝ) ^ 2) / rmin *
          (K * (9 : ℝ) ^ 12 * exp (-12 * ((n - 1 : ℕ) : ℝ) ^ 2)) := by
    apply mul_le_mul _ hlength' hlength₀ (by positivity)
    apply div_le_div_of_nonneg_right _ hrmin.le
    calc
      _ ≤ 2 * (4 * C ^ 2 * Statements.radialQ n ^ 2 * exp ((n : ℝ) ^ 2)) * contrast :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by norm_num)) hcontrast₀
      _ ≤ _ := mul_le_mul_of_nonneg_left hcontrast (by positivity)
  have hn24 : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hprevCast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hexp : 7 * (n : ℝ) ^ 2 - 12 * ((n - 1 : ℕ) : ℝ) ^ 2 ≤
      -4 * (n : ℝ) ^ 2 := by
    rw [hprevCast]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn24) (Nat.cast_nonneg (α := ℝ) n)]
  calc
    _ ≤ _ := hmain
    _ = (8 * (9 : ℝ) ^ 12 * K * C ^ 2 / rmin) * Statements.radialQ n ^ 2 *
        (exp ((n : ℝ) ^ 2) * exp (6 * (n : ℝ) ^ 2) *
          exp (-12 * ((n - 1 : ℕ) : ℝ) ^ 2)) := by ring
    _ = (8 * (9 : ℝ) ^ 12 * K * C ^ 2 / rmin) * Statements.radialQ n ^ 2 *
        exp (7 * (n : ℝ) ^ 2 - 12 * ((n - 1 : ℕ) : ℝ) ^ 2) := by
          rw [← exp_add, ← exp_add]
          congr 2
          ring
    _ ≤ (8 * (9 : ℝ) ^ 12 * K * C ^ 2 / rmin) * Statements.radialQ n ^ 2 *
        exp (-4 * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) (by positivity)
    _ = _ := rfl

private theorem r07_q_sq_exp_neg_tendsto :
    Tendsto (fun n : ℕ => Statements.radialQ n ^ 2 * exp (-(n : ℝ)))
      atTop (𝓝 0) := by
  have h := (morseTransition_deeper_bound_tendsto (1 : ℝ)).div_const 135
  convert h using 1
  · funext n
    ring
  · norm_num

private theorem r07_q_sq_exp_neg_three_sq_tendsto :
    Tendsto (fun n : ℕ => Statements.radialQ n ^ 2 * exp (-3 * (n : ℝ) ^ 2))
      atTop (𝓝 0) := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) r07_q_sq_exp_neg_tendsto
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply exp_le_exp.mpr
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    norm_num
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn1) (Nat.cast_nonneg (α := ℝ) n),
      sq_nonneg (n : ℝ)]

/-- The transfer envelope is little-o of the height-selection margin. -/
theorem r07JoinEnvelope_scaled_tendsto (K C rmin : ℝ) :
    Tendsto (fun n : ℕ => r07JoinEnvelope K C rmin n * exp ((n : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have h := r07_q_sq_exp_neg_three_sq_tendsto.const_mul
    (8 * (9 : ℝ) ^ 12 * K * C ^ 2 / rmin)
  convert h using 1
  · funext n
    unfold r07JoinEnvelope
    rw [mul_assoc, ← exp_add,
      show -4 * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 = -3 * (n : ℝ) ^ 2 by ring]
    ring
  · simp only [mul_zero]

/-- Any fixed positive multiple of `exp (-n²)` eventually dominates the
whole frequency-band transfer envelope. -/
theorem r07JoinEnvelope_eventually_small (K C rmin : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop,
      r07JoinEnvelope K C rmin n < (c₀ * exp (-(n : ℝ) ^ 2)) / 12 := by
  filter_upwards [(r07JoinEnvelope_scaled_tendsto K C rmin).eventually
    (eventually_lt_nhds (div_pos hc₀ (by norm_num : (0 : ℝ) < 12)))] with n hn
  calc
    _ = (r07JoinEnvelope K C rmin n * exp ((n : ℝ) ^ 2)) * exp (-(n : ℝ) ^ 2) := by
      rw [mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
    _ < (c₀ / 12) * exp (-(n : ℝ) ^ 2) := mul_lt_mul_of_pos_right hn (exp_pos _)
    _ = _ := by ring

/-- The pointwise join hypotheses give a uniform small action for all
frequencies in all sufficiently late bands. -/
theorem r07_join_action_eventually_small (T : Statements.MorseChainData)
    {C K rmin c₀ : ℝ} (hC : 0 < C) (hK : 0 ≤ K) (hrmin : 0 < rmin)
    (hc₀ : 0 < c₀) (hd : ∀ n, T.index ≤ n → T.d n = morseChainInteger n) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, Statements.radialFrequencyBand T C n j →
      ∀ contrast length : ℝ, 0 ≤ contrast → contrast ≤ exp (6 * (n : ℝ) ^ 2) →
        0 ≤ length → length ≤ K * Statements.morseChainA T (n - 1) ^ 12 →
          2 * (j : ℝ) ^ 2 * contrast / rmin * length <
            (c₀ * exp (-(n : ℝ) ^ 2)) / 12 := by
  filter_upwards [eventually_ge_atTop 24, eventually_gt_atTop T.index,
    r07JoinEnvelope_eventually_small K C rmin hc₀] with n hn hprev hsmall
  intro j hband contrast length hcontrast₀ hcontrast hlength₀ hlength
  exact (r07_join_action_le T hC hK hrmin hd hn hprev hband
    hcontrast₀ hcontrast hlength₀ hlength).trans_lt hsmall

/-- Convert a small transfer action to the coordinate error allowed in
the height-exclusion theorem. -/
theorem r07_transfer_error_le_margin {action margin : ℝ}
    (haction : 0 ≤ action) (hmargin : margin ≤ 1) (hsmall : action ≤ margin / 12) :
    (exp action - 1) * (3 / 2 : ℝ) ≤ margin / 4 := by
  have ha1 : |action| ≤ 1 := by rw [abs_of_nonneg haction]; linarith
  have he : exp action - 1 ≤ 2 * action := by
    have h := abs_exp_sub_one_le ha1
    rw [abs_of_nonneg haction] at h
    exact (le_abs_self _).trans h
  linarith

/-- A normalized incoming state with slope in the prescribed compact
interval satisfies the required coordinate estimates after a small join.
The starting and ending radii may occur in either order. -/
theorem r07_joinState_close {J W contrast r₀ r₁ s t a margin : ℝ}
    {w u : ℝ → ℝ} (hr₀ : 0 < r₀) (hJ : 1 ≤ J) (hW : 0 < W)
    (hcontrast : 1 ≤ contrast)
    (hreg : ∀ r ∈ Icc r₀ r₁, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ u r ∧
      DifferentiableAt ℝ (deriv u) r)
    (hw : ∀ r ∈ Icc r₀ r₁,
      0 < w r ∧ w r ≤ contrast * W ∧ W ≤ contrast * w r)
    (hode : ∀ r ∈ Icc r₀ r₁, radialJacobi J w u r = 0)
    (hs : s ∈ Icc r₀ r₁) (ht : t ∈ Icc r₀ r₁)
    (hstart : joinState J W w u s = (1, a))
    (ha : a ∈ Icc (-(3 : ℝ) / 2) (-1 / 2)) (hmargin : margin ≤ 1)
    (hsmall : 2 * J * contrast / r₀ * |t - s| ≤ margin / 12) :
    |(joinState J W w u t).1 - 1| ≤ margin / 4 ∧
      |(joinState J W w u t).2 - a| ≤ margin / 4 := by
  have hnorm : ‖joinState J W w u s‖ ≤ (3 / 2 : ℝ) := by
    rw [hstart, norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨by norm_num, abs_le.mpr ⟨ha.1, ha.2.trans (by norm_num)⟩⟩
  have haction : 0 ≤ 2 * J * contrast / r₀ * |t - s| := by
    have hJ₀ : 0 ≤ J := zero_le_one.trans hJ
    have hcontrast₀ : 0 ≤ contrast := zero_le_one.trans hcontrast
    positivity
  have herror :
      (exp (2 * J * contrast / r₀ * |t - s|) - 1) * ‖joinState J W w u s‖ ≤
        margin / 4 := by
    calc
      _ ≤ (exp (2 * J * contrast / r₀ * |t - s|) - 1) * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr (one_le_exp_iff.mpr haction))
      _ ≤ _ := r07_transfer_error_le_margin haction hmargin hsmall
  obtain ⟨hfirst, hsecond⟩ := joinState_transfer_coord hr₀ hJ hW hcontrast hreg hw hode s hs t ht
  rw [hstart] at hfirst hsecond herror
  exact ⟨hfirst.trans herror, hsecond.trans herror⟩

end ContinuousFlexibility.Radial
