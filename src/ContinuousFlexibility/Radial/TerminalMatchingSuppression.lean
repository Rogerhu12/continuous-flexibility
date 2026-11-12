import ContinuousFlexibility.Radial.MorseTransitionBands
import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Parameter absorption at the terminal matching cuts

The action and margin in this file are the actual Morse action
j * sqrt (A_m) and the selected margin c₀ * exp (-n²). The threshold
constant is chosen from the coefficient exponent and the decay rate first.
The transition growth constant and the selected margin then determine a
first index. The initial band is controlled separately by a long head.

These are scalar estimates. Applying them to a matching matrix still
requires the actual Poisson error and outer propagation estimates on the
same geometry; no such differential estimate is included as a conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real
open scoped Topology

def terminalMatchingAction (T : Statements.MorseChainData) (m j : ℕ) : ℝ :=
  (j : ℝ) * sqrt (Statements.morseChainA T m)

theorem terminalMatchingAction_nonneg (T : Statements.MorseChainData) (m j : ℕ) :
    0 ≤ terminalMatchingAction T m j :=
  mul_nonneg (Nat.cast_nonneg j) (sqrt_nonneg _)

def terminalMatchingMargin (c₀ : ℝ) (n : ℕ) : ℝ :=
  c₀ * exp (-(n : ℝ) ^ 2)

theorem terminalMatchingMargin_pos {c₀ : ℝ} (hc₀ : 0 < c₀) (n : ℕ) :
    0 < terminalMatchingMargin c₀ n := mul_pos hc₀ (exp_pos _)

theorem terminalMatching_factor_eq_exp (n : ℕ) (C Co c t u : ℝ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Statements.radialE n ^ C * (terminalMatchingMargin c₀ n)⁻¹ *
      exp (Co * u - c * t) =
        exp (C * Statements.radialQ n + (n : ℝ) ^ 2 - log c₀ + Co * u - c * t) := by
  have hm : terminalMatchingMargin c₀ n = exp (log c₀ - (n : ℝ) ^ 2) := by
    rw [terminalMatchingMargin, sub_eq_add_neg, exp_add, exp_log hc₀]
  rw [Statements.radialE, ← exp_mul, hm, ← exp_neg, ← exp_add, ← exp_add]
  congr 1
  ring

/-- Four separate quarters pay for the coefficient power, the Gaussian
margin, its constant, and propagation through the transition cell. -/
theorem terminalMatching_small_of_quarter_budgets (n : ℕ)
    {C Co c c₀ t u : ℝ} (hc₀ : 0 < c₀)
    (hcoefficient : C * Statements.radialQ n ≤ c * t / 4)
    (hindex : (n : ℝ) ^ 2 ≤ c * t / 4)
    (hmargin : |log c₀| + log 16 + 1 ≤ c * t / 4)
    (hpropagation : Co * u ≤ c * t / 4) :
    Statements.radialE n ^ C * (terminalMatchingMargin c₀ n)⁻¹ *
      exp (Co * u - c * t) < 1 / 16 := by
  rw [terminalMatching_factor_eq_exp n C Co c t u hc₀]
  have he : C * Statements.radialQ n + (n : ℝ) ^ 2 - log c₀ + Co * u - c * t <
      -log 16 := by linarith only [neg_le_abs (log c₀), hcoefficient, hindex,
        hmargin, hpropagation]
  calc
    _ < exp (-log 16) := exp_lt_exp.mpr he
    _ = 1 / 16 := by rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 16)]; norm_num

/-- Two independently decaying columns obey the margin-sixteenth bound
as soon as each has at least the preceding-cell action. -/
theorem terminalMatching_two_attenuations (n : ℕ) {C Co c c₀ t u r s : ℝ}
    (hc₀ : 0 < c₀) (hc : 0 ≤ c) (hCo : 0 ≤ Co) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hr : t ≤ r) (hs : t ≤ s)
    (hsmall : Statements.radialE n ^ C * (terminalMatchingMargin c₀ n)⁻¹ *
      exp (Co * u - c * t) < 1 / 16) :
    Statements.radialE n ^ C * exp (-c * r - c * s) < terminalMatchingMargin c₀ n / 16 := by
  have he : -c * r - c * s ≤ Co * u - c * t := by
    nlinarith only [mul_le_mul_of_nonneg_left hr hc,
      mul_le_mul_of_nonneg_left hs hc, mul_nonneg hc ht, mul_nonneg hCo hu]
  have hratio : Statements.radialE n ^ C * exp (-c * r - c * s) /
      terminalMatchingMargin c₀ n < 1 / 16 := by
    calc
      _ = Statements.radialE n ^ C * (terminalMatchingMargin c₀ n)⁻¹ *
          exp (-c * r - c * s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by
        exact mul_nonneg (rpow_nonneg (exp_pos _).le _) (inv_pos.mpr
          (terminalMatchingMargin_pos hc₀ n)).le)
      _ < _ := hsmall
  have h := (div_lt_iff₀ (terminalMatchingMargin_pos hc₀ n)).mp hratio
  linarith only [h]

/-- A coarse adjacent coefficient ratio suffices for the choice order;
the sharper asymptotic ratio one is unnecessary. -/
theorem terminalMatching_radialQ_succ_le {m : ℕ} (hm : 1 ≤ m) :
    Statements.radialQ (m + 1) ≤ 16 * Statements.radialQ m := by
  have hx : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx₀ : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog₀ := ssv_one_le_log hx₀
  have he : (1 : ℝ) ≤ exp 1 + m := by
    have := (one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1))
    linarith only [this, hx₀]
  have hi : 1 / (exp 1 + (m : ℝ)) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) he
  have hlog : log (exp 1 + ((m : ℝ) + 1)) ≤ 2 * log (exp 1 + m) := by
    linarith only [ssv_log_succ_sub_le hx₀, hi, hlog₀]
  have hsq : ((m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hx]) 2
  have hsqrt : sqrt ((m : ℝ) + 1) ≤ 2 * sqrt (m : ℝ) := by
    apply (sqrt_le_left (by positivity)).mpr
    rw [mul_pow, sq_sqrt hx₀]
    nlinarith only [hx]
  calc
    Statements.radialQ (m + 1) =
        (((m : ℝ) + 1) ^ 2 * sqrt ((m : ℝ) + 1)) * log (exp 1 + ((m : ℝ) + 1)) := by
      simp only [Statements.radialQ, Nat.cast_add, Nat.cast_one,
        ssv_rpow_five_half (by positivity : 0 ≤ (m : ℝ) + 1)]
    _ ≤ ((2 * (m : ℝ)) ^ 2 * (2 * sqrt (m : ℝ))) * (2 * log (exp 1 + m)) :=
      mul_le_mul (mul_le_mul hsq hsqrt (sqrt_nonneg _) (sq_nonneg _)) hlog
        (zero_le_one.trans (ssv_one_le_log (by positivity : 0 ≤ (m : ℝ) + 1))) (by positivity)
    _ = 16 * Statements.radialQ m := by
      rw [Statements.radialQ, ssv_rpow_five_half hx₀]
      ring

/-- The actual adjacent Morse-scale ratio absorbs any fixed propagation
constant, uniformly over every frequency. -/
theorem terminalMatching_adjacent_action_small (T : Statements.MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {c Co : ℝ} (hc : 0 < c) (hCo : 0 ≤ Co) :
    ∀ᶠ m : ℕ in atTop, ∀ j : ℕ,
      Co * terminalMatchingAction T (m + 1) j ≤ c * terminalMatchingAction T m j / 4 := by
  have hden : 0 < 4 * (Co + 1) := by positivity
  have hε : 0 < (c / (4 * (Co + 1))) ^ 2 := sq_pos_of_pos (div_pos hc hden)
  filter_upwards [eventually_ge_atTop T.index, eventually_ge_atTop 1,
    (morseTransition_next_ratio_tendsto T hd).eventually (eventually_lt_nhds hε)]
      with m hm hm1 hsmall
  have hAm : 0 < Statements.morseChainA T m :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T m (hd m hm)).1
  have hAs : 0 < Statements.morseChainA T (m + 1) :=
    (div_pos (exp_pos _) (by norm_num : (0 : ℝ) < 3)).trans_le
      (morseChainA_exp_bounds T (m + 1) (hd (m + 1) (hm.trans (Nat.le_succ m)))).1
  have hx : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hq : 1 ≤ Statements.radialQ m := by
    nlinarith only [radial_nat_sq_le_Q m, sq_nonneg ((m : ℝ) - 1), hx]
  have hq₂ : 1 ≤ Statements.radialQ m ^ 2 := by nlinarith only [hq]
  have hr₀ : 0 ≤ Statements.morseChainA T (m + 1) / Statements.morseChainA T m := by positivity
  have hr : Statements.morseChainA T (m + 1) / Statements.morseChainA T m ≤
      (c / (4 * (Co + 1))) ^ 2 := by
    refine le_trans ?_ hsmall.le
    have h₁ := mul_nonneg (sub_nonneg.mpr hq₂) hr₀
    have h₂ := mul_nonneg (mul_nonneg (sq_nonneg (Statements.radialQ m)) hr₀)
      (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [h₁, h₂]
  have hs := (sqrt_le_left (div_pos hc hden).le).mpr hr
  rw [sqrt_div hAs.le] at hs
  have hcross := (div_le_div_iff₀ (sqrt_pos.mpr hAm) hden).mp hs
  intro j
  have hj := mul_le_mul_of_nonneg_right hcross (Nat.cast_nonneg (α := ℝ) j)
  have hj₀ := mul_nonneg (sqrt_nonneg (Statements.morseChainA T (m + 1)))
    (Nat.cast_nonneg (α := ℝ) j)
  dsimp only [terminalMatchingAction]
  nlinarith only [hj, hj₀]

/-- Choose the band threshold before the selected margin and the outer
growth constant. One index controls the ratio and both column attenuations
for every later band and every frequency in that band. -/
theorem exists_terminalMatching_band_suppression (T : Statements.MorseChainData)
    (hd : ∀ m, T.index ≤ m → T.d m = morseChainInteger m)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ Co : ℝ, 0 ≤ Co → ∀ c₀ : ℝ, 0 < c₀ →
      ∃ N : ℕ, T.index ≤ N ∧ ∀ m : ℕ, N ≤ m → ∀ j : ℕ,
        Statements.radialFrequencyBand T Cstar (m + 1) j →
        (Statements.radialE (m + 1) ^ C * (terminalMatchingMargin c₀ (m + 1))⁻¹ *
          exp (Co * terminalMatchingAction T (m + 1) j -
            c * terminalMatchingAction T m j) < 1 / 16) ∧
        ∀ r s : ℝ, terminalMatchingAction T m j ≤ r → terminalMatchingAction T m j ≤ s →
          Statements.radialE (m + 1) ^ C * exp (-c * r - c * s) <
            terminalMatchingMargin c₀ (m + 1) / 16 := by
  let Cstar : ℝ := (64 * C + 16) / c
  have hCstar : 0 < Cstar := div_pos (by positivity) hc
  have hscale : c * Cstar = 64 * C + 16 := by
    dsimp only [Cstar]
    field_simp [hc.ne'] <;> ring
  refine ⟨Cstar, hCstar, ?_⟩
  intro Co hCo c₀ hc₀
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (|log c₀| + log 16 + 1)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (terminalMatching_adjacent_action_small T hd hc hCo)
  refine ⟨max T.index (max 1 (max N₀ N₁)), by omega, ?_⟩
  intro m hm j hband
  have hmIndex : T.index ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hx : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hq₀ := radialQ_nonneg m
  have ht := mul_le_mul_of_nonneg_left
    (morseTransition_earlier_cap_action T hCstar hd hband hmIndex (Nat.lt_succ_self m)) hc.le
  rw [← mul_assoc, hscale] at ht
  have hcoeff := mul_le_mul_of_nonneg_left (terminalMatching_radialQ_succ_le hm1) hC
  have hCQ := mul_nonneg hC hq₀
  have hsq : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * Statements.radialQ m := by
    have h := mul_nonneg (sub_nonneg.mpr hx) (by positivity : 0 ≤ 3 * (m : ℝ) + 1)
    push_cast
    nlinarith only [h, radial_nat_sq_le_Q m]
  have hlog : |log c₀| + log 16 + 1 ≤ Statements.radialQ m := by
    have hcast := hN₀.trans (Nat.cast_le.mpr (by omega : N₀ ≤ m))
    have h := mul_nonneg (sub_nonneg.mpr hx) (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hcast, h, radial_nat_sq_le_Q m]
  have hsmall : Statements.radialE (m + 1) ^ C * (terminalMatchingMargin c₀ (m + 1))⁻¹ *
      exp (Co * terminalMatchingAction T (m + 1) j - c * terminalMatchingAction T m j) <
        1 / 16 := by
    apply terminalMatching_small_of_quarter_budgets (m + 1) hc₀
    · dsimp only [terminalMatchingAction]
      nlinarith only [hcoeff, ht, hq₀]
    · dsimp only [terminalMatchingAction]
      nlinarith only [hsq, ht, hCQ]
    · dsimp only [terminalMatchingAction]
      nlinarith only [hlog, ht, hCQ, hq₀]
    · exact hN₁ m (by omega) j
  refine ⟨hsmall, ?_⟩
  intro r s hr hs
  exact terminalMatching_two_attenuations (m + 1) hc₀ hc.le hCo
    (terminalMatchingAction_nonneg T m j) (terminalMatchingAction_nonneg T (m + 1) j)
    hr hs hsmall

/-- At the first band the preceding action is j * L. One fixed head
length controls every positive frequency, including the entire band. -/
theorem exists_terminalMatching_first_band_suppression
    (T : Statements.MorseChainData) (n : ℕ) (C Co : ℝ)
    {c c₀ : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ j : ℕ, 1 ≤ j →
      Statements.radialE n ^ C * (terminalMatchingMargin c₀ n)⁻¹ *
        exp (Co * terminalMatchingAction T n j - c * ((j : ℝ) * L)) < 1 / 16 := by
  let r : ℝ := C * Statements.radialQ n + (n : ℝ) ^ 2 - log c₀
  let a : ℝ := Co * sqrt (Statements.morseChainA T n)
  let K : ℝ := |r| + |a| + log 16 + 1
  refine ⟨max 1 (K / c), le_max_left _ _, ?_⟩
  intro L hL j hj
  have hKL : K ≤ L * c := (div_le_iff₀ hc).mp ((le_max_right 1 (K / c)).trans hL)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog₀ : 0 ≤ log (16 : ℝ) := log_nonneg (by norm_num)
  have hrest : |r| + log 16 + 1 ≤ (j : ℝ) * (|r| + log 16 + 1) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hj1)
      (by positivity : 0 ≤ |r| + log 16 + 1)]
  have hb := mul_le_mul_of_nonneg_left hKL hj₀
  have ha := mul_le_mul_of_nonneg_left (le_abs_self a) hj₀
  rw [terminalMatching_factor_eq_exp n C Co c _ _ hc₀]
  have he : C * Statements.radialQ n + (n : ℝ) ^ 2 - log c₀ +
      Co * terminalMatchingAction T n j - c * ((j : ℝ) * L) < -log 16 := by
    change r + Co * ((j : ℝ) * sqrt (Statements.morseChainA T n)) - c * ((j : ℝ) * L) < _
    have haction : Co * ((j : ℝ) * sqrt (Statements.morseChainA T n)) = (j : ℝ) * a := by
      dsimp only [a]
      ring
    rw [haction]
    dsimp only [K] at hb
    nlinarith only [hb, ha, hrest, le_abs_self r]
  calc
    _ < exp (-log 16) := exp_lt_exp.mpr he
    _ = 1 / 16 := by rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 16)]; norm_num

end ContinuousFlexibility.Radial
