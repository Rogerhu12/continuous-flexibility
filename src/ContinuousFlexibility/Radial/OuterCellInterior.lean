import ContinuousFlexibility.Radial.OuterInteriorEnergy
import ContinuousFlexibility.Radial.OuterCellScale
import Mathlib.Topology.Order.IntermediateValue

/-!
# Pointwise growth through a complete retained Morse cell

The model estimates cover arbitrary points, including either cap and
the negative component.  The actual radius chart is surjective onto
its retained physical interval, so the same estimate holds for every
actual physical state there.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem morsePositiveEnergyFactor_one_le {A B j l r : ℝ}
    (hlr : l ≤ r) (hρ : ∀ x ∈ Icc l r, 0 ≤ -morseRho A B x) :
    1 ≤ morsePositiveEnergyFactor A B j l r := by
  have hI : 0 ≤ ∫ x in l..r, -morseRho A B x := intervalIntegral.integral_nonneg hlr hρ
  have hb : 1 ≤ 1 + (r - l) + j ^ 2 * (∫ x in l..r, -morseRho A B x) := by
    have hp := mul_nonneg (sq_nonneg j) hI
    linarith only [sub_nonneg.mpr hlr, hp]
  have hp : 1 ≤ (1 + (r - l) + j ^ 2 * (∫ x in l..r, -morseRho A B x)) ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hb 4
  have he : 1 ≤ exp (2 * sqrt ((r - l) * (j ^ 2 * (∫ x in l..r, -morseRho A B x))) + 2) :=
    one_le_exp_iff.mpr (by positivity)
  exact (by simpa only [one_mul] using mul_le_mul hp he zero_le_one (by positivity) :
    1 ≤ (1 + (r - l) + j ^ 2 * (∫ x in l..r, -morseRho A B x)) ^ 4 *
      exp (2 * sqrt ((r - l) * (j ^ 2 * (∫ x in l..r, -morseRho A B x))) + 2))

theorem morseNegativeEnergyFactor_one_le {A B : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (j : ℝ) : 1 ≤ morseNegativeEnergyFactor A B j := by
  have hp : 0 ≤ A / 4 - B := by linarith only [hAB]
  have hq : 1 ≤ 1 + j ^ 2 * (A / 4 - B) :=
    le_add_of_nonneg_right (mul_nonneg (sq_nonneg j) hp)
  exact one_le_exp_iff.mpr (add_nonneg (sub_nonneg.mpr (morseTurn_order hB hAB).le)
    (mul_nonneg (by norm_num) (log_nonneg hq)))

theorem morse_positive_energy_on {A B j l r s t : ℝ} {u v : ℝ → ℝ}
    (hlr : l ≤ r) (hρ : ∀ x ∈ Icc l r, 0 ≤ -morseRho A B x)
    (hu : ∀ x ∈ Icc l r, HasDerivAt u (v x) x)
    (hv : ∀ x ∈ Icc l r, HasDerivAt v (-(j ^ 2 * morseRho A B x * u x)) x)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    u t ^ 2 + v t ^ 2 ≤ (u s ^ 2 + v s ^ 2) * morsePositiveEnergyFactor A B j l r := by
  have hρc : Continuous (morseRho A B) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt
  have hstate (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivAt u ((1 : ℝ) * v x) x ∧
        HasDerivAt v ((j ^ 2 * -morseRho A B x) * u x) x := by
    exact ⟨by simpa only [one_mul] using hu x hx, (hv x hx).congr_deriv (by ring)⟩
  have hh := transfer_positive_piece_regularized_on hlr continuousOn_const
    (continuous_const.mul hρc.neg).continuousOn (fun _ _ => zero_le_one)
    (fun x hx => mul_nonneg (sq_nonneg j) (hρ x hx)) hstate hs ht
  simpa only [morsePositiveEnergyFactor, intervalIntegral.integral_const,
    smul_eq_mul, mul_one, Pi.mul_apply, Pi.neg_apply, intervalIntegral.integral_const_mul] using hh

theorem morse_cell_energy_on {A B j c s t : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (hc : 0 ≤ c) {u v : ℝ → ℝ}
    (hu : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B c), HasDerivAt u (v x) x)
    (hv : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B c),
      HasDerivAt v (-(j ^ 2 * morseRho A B x * u x)) x)
    (hs : s ∈ Icc morseCellLeftCut (morseRightCapEnd A B c))
    (ht : t ∈ Icc morseCellLeftCut (morseRightCapEnd A B c)) :
    u t ^ 2 + v t ^ 2 ≤ (u s ^ 2 + v s ^ 2) *
      ((1 + j ^ 2 * (A / 4 - B)) * morseCellEnergyFactor A B j c) := by
  let a := morseCellLeftCut
  let l := morseLeftTurn A B
  let r := morseRightTurn A B
  let e := morseRightCapEnd A B c
  let E (x : ℝ) := u x ^ 2 + v x ^ 2
  let Kl := morsePositiveEnergyFactor A B j a l
  let Kn := (1 + j ^ 2 * (A / 4 - B)) * morseNegativeEnergyFactor A B j
  let Kr := morsePositiveEnergyFactor A B j r e
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hal : a ≤ l := (morseCellLeftCut_lt_leftTurn hB hAB).le
  have hlr : l ≤ r := (morseTurn_order hB hAB).le
  have hre : r ≤ e := by
    change r ≤ r + c / A ^ 4
    exact le_add_of_nonneg_right (div_nonneg hc (pow_nonneg hA.le 4))
  have hsL : Icc a l ⊆ Icc a e := Icc_subset_Icc_right (hlr.trans hre)
  have hsN : Icc l r ⊆ Icc a e := Icc_subset_Icc hal hre
  have hsR : Icc r e ⊆ Icc a e := Icc_subset_Icc_left (hal.trans hlr)
  have hρL (x : ℝ) (hx : x ∈ Icc a l) : 0 ≤ -morseRho A B x := by
    rcases hx.2.eq_or_lt with heq | hlt
    · rw [(morseRho_zero_iff_turn hB hAB x).mpr (Or.inl heq)]
      simp
    · exact neg_nonneg.mpr (morseRho_neg_before_left_turn hB hAB hlt).le
  have hleft : ∀ s ∈ Icc a l, ∀ t ∈ Icc a l, E t ≤ E s * Kl :=
    fun s hs t ht => morse_positive_energy_on hal hρL
      (fun x hx => hu x (hsL hx)) (fun x hx => hv x (hsL hx)) hs ht
  have hnegative : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, E t ≤ E s * Kn :=
    fun s hs t ht => morse_negative_energy_on hB hAB
      (fun x hx => hu x (hsN hx)) (fun x hx => hv x (hsN hx)) hs ht
  have hright : ∀ s ∈ Icc r e, ∀ t ∈ Icc r e, E t ≤ E s * Kr :=
    fun s hs t ht => morse_positive_energy_on hre
      (fun x hx => (morseRho_right_cap_bounds hB hAB hx.1).1)
      (fun x hx => hu x (hsR hx)) (fun x hx => hv x (hsR hx)) hs ht
  have hKl : 1 ≤ Kl := morsePositiveEnergyFactor_one_le hal hρL
  have hKn : 1 ≤ Kn := by
    have hp : 0 ≤ A / 4 - B := by linarith only [hAB]
    have hq : 1 ≤ 1 + j ^ 2 * (A / 4 - B) :=
      le_add_of_nonneg_right (mul_nonneg (sq_nonneg j) hp)
    simpa only [one_mul] using mul_le_mul hq (morseNegativeEnergyFactor_one_le hB hAB j)
      zero_le_one (by positivity)
  have hKr : 1 ≤ Kr := morsePositiveEnergyFactor_one_le hre
    (fun x hx => (morseRho_right_cap_bounds hB hAB hx.1).1)
  have hfirst : ∀ s ∈ Icc a r, ∀ t ∈ Icc a r, E t ≤ E s * (Kl * Kn) :=
    fun s hs t ht => energy_transfer_join hal hlr hKl hKn (fun x _ => by dsimp only [E]; positivity)
      hleft hnegative hs ht
  have hKlKn : 1 ≤ Kl * Kn := by
    simpa only [one_mul] using mul_le_mul hKl hKn zero_le_one (zero_le_one.trans hKl)
  have hh := energy_transfer_join (hal.trans hlr) hre hKlKn hKr
    (fun x _ => show 0 ≤ E x by dsimp only [E]; positivity) hfirst hright hs ht
  calc
    _ ≤ E s * ((Kl * Kn) * Kr) := hh
    _ = _ := by dsimp only [E, Kl, Kn, Kr, a, l, r, e, morseCellEnergyFactor]; ring

theorem outer_morse_peak_factor_le {T : MorseChainData} {C : ℝ} {n j : ℕ}
    (hn : 1 ≤ n) (hd : T.d n = morseChainInteger n)
    (hband : radialFrequencyBand T C n j) :
    1 + (j : ℝ) ^ 2 * (morseChainA T n / 4 - morseChainB T n) ≤
      exp ((outerFrequencyExponent C + 10) * (n : ℝ) ^ 2) := by
  let F := outerFrequencyExponent C
  let N := (n : ℝ) ^ 2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ N := by dsimp only [N]; nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
  have hF : 0 ≤ F := by dsimp only [F, outerFrequencyExponent]; positivity
  have hA := morseChainA_le_nine T n hd
  have hB : 0 ≤ morseChainB T n := by unfold morseChainB; positivity
  have hpeak : morseChainA T n / 4 - morseChainB T n ≤ 9 := by linarith only [hA, hB]
  have hj2 := outer_frequency_sq_le_exp hn hd hband
  have hp := mul_le_mul_of_nonneg_left hpeak (sq_nonneg (j : ℝ))
  have hj := mul_le_mul_of_nonneg_right hj2 (by norm_num : (0 : ℝ) ≤ 9)
  have he : 1 ≤ exp (F * N) := one_le_exp_iff.mpr (mul_nonneg hF (zero_le_one.trans hN))
  have h10 : (10 : ℝ) ≤ exp (10 * N) :=
    (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 10) hN).trans
      ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
  calc
    _ ≤ 10 * exp (F * N) := by nlinarith only [hp, hj, he]
    _ ≤ exp (10 * N) * exp (F * N) := mul_le_mul_of_nonneg_right h10 (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; dsimp only [F, N]; ring

theorem morseRealized_cell_energy_on {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {j scale M s t : ℝ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (hM : 1 ≤ M)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n)
    (hhi : scale / morseChainAmplitude T σ n ≤ M)
    (hlo : morseChainAmplitude T σ n / scale ≤ M)
    (hstate : ∀ r ∈ Icc (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z (j ^ 2 * deriv D.w r / (scale * r) * u r) r)
    (hs : s ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n)))
    (ht : t ∈ Icc (T.radius side n (T.leftX side n)) (T.radius side n (T.rightX side n))) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      (M ^ 4 * ((1 + j ^ 2 * (morseChainA T n / 4 - morseChainB T n)) *
        morseCellEnergyFactor (morseChainA T n) (morseChainB T n) j (1 / 100))) := by
  let R := T.radius side n
  let q := scale / morseChainAmplitude T σ n
  let F := (1 + j ^ 2 * (morseChainA T n / 4 - morseChainB T n)) *
    morseCellEnergyFactor (morseChainA T n) (morseChainB T n) j (1 / 100)
  have hlam : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hq : 0 < q := div_pos hscale hlam
  have hret := h.retained_data side n hn
  have hab : T.leftX side n ≤ T.rightX side n :=
    (hret.2.2.2.1.trans hret.2.2.2.2.1).le
  have hsurj := intermediate_value_Icc hab (h.radius_smooth side n hn).continuous.continuousOn
  obtain ⟨X, hX, hsX⟩ := hsurj hs
  obtain ⟨Y, hY, htY⟩ := hsurj ht
  have hl : T.leftX side n = morseCellLeftCut := hret.2.2.1
  have hr : T.rightX side n =
      morseRightCapEnd (morseChainA T n) (morseChainB T n) (1 / 100) := by
    simpa only [morseRightCapEnd, morseRightCapLength, morseChainRightTurn,
      morseRightTurn, morseRightRootT] using hret.2.2.2.2.2.1
  have hp := morseRealized_state_pullback h hσ hscale side n hn hstate
  rw [hl, hr] at hp hX hY
  have he := morse_cell_energy_on (j := j) hret.1 hret.2.1
    (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (fun x hx => (hp x hx).1) (fun x hx => (hp x hx).2) hX hY
  rw [hsX, htY] at he
  have hweighted : u t ^ 2 + q ^ 2 * z t ^ 2 ≤ (u s ^ 2 + q ^ 2 * z s ^ 2) * F := by
    simpa only [mul_pow, q, F] using he
  have hqhi : q ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hq.le hhi 2
  have hprod : 1 ≤ M * q := by
    have hh := mul_le_mul_of_nonneg_right hlo hq.le
    have heq : (morseChainAmplitude T σ n / scale) * q = 1 := by
      dsimp only [q]
      field_simp [hscale.ne', hlam.ne']
    rw [heq] at hh
    exact hh
  have hqlo : 1 ≤ M ^ 2 * q ^ 2 := by
    simpa only [one_pow, mul_pow] using pow_le_pow_left₀ zero_le_one hprod 2
  have hpeak : 0 ≤ morseChainA T n / 4 - morseChainB T n := by linarith only [hret.2.1]
  have hF : 0 ≤ F := mul_nonneg (by positivity) (morseCellEnergyFactor_nonneg _ _ _ _)
  simpa only [mul_assoc] using state_energy_rescale_transfer hM hqhi hqlo hF hweighted

end ContinuousFlexibility.Radial
