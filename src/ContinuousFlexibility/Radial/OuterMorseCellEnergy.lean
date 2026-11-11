import ContinuousFlexibility.Radial.OuterMorseEnergy
import ContinuousFlexibility.Radial.OuterPositiveTransfer

/-!
# Energy across one entire retained Morse cell

The two positive caps and the negative component are traversed in either
direction.  All three pieces use the same actual solution of the model
equation; the transfer factors are derived from its coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory

def morsePositiveEnergyFactor (A B j l r : ℝ) : ℝ :=
  let I := ∫ x in l..r, -morseRho A B x
  (1 + (r - l) + j ^ 2 * I) ^ 4 * exp (2 * sqrt ((r - l) * (j ^ 2 * I)) + 2)

def morseNegativeEnergyFactor (A B j : ℝ) : ℝ :=
  exp (morseRightTurn A B - morseLeftTurn A B +
    2 * log (1 + j ^ 2 * (A / 4 - B)))

def morseCellEnergyFactor (A B j c : ℝ) : ℝ :=
  morsePositiveEnergyFactor A B j morseCellLeftCut (morseLeftTurn A B) *
    morseNegativeEnergyFactor A B j *
    morsePositiveEnergyFactor A B j (morseRightTurn A B) (morseRightCapEnd A B c)

theorem morsePositiveEnergyFactor_nonneg (A B j l r : ℝ) :
    0 ≤ morsePositiveEnergyFactor A B j l r := by
  unfold morsePositiveEnergyFactor
  positivity

theorem morse_positive_endpoint_energy {A B j l r : ℝ} {u v : ℝ → ℝ}
    (hlr : l ≤ r) (hρ : ∀ x ∈ Icc l r, 0 ≤ -morseRho A B x)
    (hu : ∀ x ∈ Icc l r, HasDerivAt u (v x) x)
    (hv : ∀ x ∈ Icc l r, HasDerivAt v (-(j ^ 2 * morseRho A B x * u x)) x) :
    (u r ^ 2 + v r ^ 2 ≤ (u l ^ 2 + v l ^ 2) * morsePositiveEnergyFactor A B j l r) ∧
      (u l ^ 2 + v l ^ 2 ≤ (u r ^ 2 + v r ^ 2) * morsePositiveEnergyFactor A B j l r) := by
  have hρc : Continuous (morseRho A B) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_morseRho A B x).continuousAt
  have hstate (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivAt u ((1 : ℝ) * v x) x ∧
        HasDerivAt v ((j ^ 2 * -morseRho A B x) * u x) x := by
    exact ⟨by simpa only [one_mul] using hu x hx, (hv x hx).congr_deriv (by ring)⟩
  have h := transfer_positive_piece_regularized hlr continuousOn_const
    (continuous_const.mul hρc.neg).continuousOn (fun _ _ => zero_le_one)
    (fun x hx => mul_nonneg (sq_nonneg j) (hρ x hx)) hstate
  simpa only [morsePositiveEnergyFactor, intervalIntegral.integral_const,
    smul_eq_mul, mul_one, Pi.mul_apply, Pi.neg_apply,
    intervalIntegral.integral_const_mul] using h

theorem morseCellLeftCut_lt_leftTurn {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    morseCellLeftCut < morseLeftTurn A B := by
  have hc : morseCellLeftCut < 0 := neg_neg_of_pos (log_pos (by norm_num))
  have ht : 0 < morseLeftTurn A B := neg_pos.mpr (log_neg
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (morseRootT_bounds hB hAB).2.2.1)
    (morseRootT_bounds hB hAB).2.2.2)
  exact hc.trans ht

/-- The whole retained model cell has one two-direction estimate, with
both caps and the oscillatory component present. -/
theorem morse_cell_endpoint_energy {A B j c : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (hc : 0 ≤ c) {u v : ℝ → ℝ}
    (hu : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B c), HasDerivAt u (v x) x)
    (hv : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B c),
      HasDerivAt v (-(j ^ 2 * morseRho A B x * u x)) x) :
    (u (morseRightCapEnd A B c) ^ 2 + v (morseRightCapEnd A B c) ^ 2 ≤
      (u morseCellLeftCut ^ 2 + v morseCellLeftCut ^ 2) * morseCellEnergyFactor A B j c) ∧
    (u morseCellLeftCut ^ 2 + v morseCellLeftCut ^ 2 ≤
      (u (morseRightCapEnd A B c) ^ 2 + v (morseRightCapEnd A B c) ^ 2) *
        morseCellEnergyFactor A B j c) := by
  let a := morseCellLeftCut
  let l := morseLeftTurn A B
  let r := morseRightTurn A B
  let e := morseRightCapEnd A B c
  let E (x : ℝ) := u x ^ 2 + v x ^ 2
  let Kl := morsePositiveEnergyFactor A B j a l
  let Kn := morseNegativeEnergyFactor A B j
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
  have hleft : E l ≤ E a * Kl ∧ E a ≤ E l * Kl :=
    morse_positive_endpoint_energy hal hρL
      (fun x hx => hu x (hsL hx)) (fun x hx => hv x (hsL hx))
  have hnegative : E r ≤ E l * Kn ∧ E l ≤ E r * Kn := by
    simpa only [E, Kn, morseNegativeEnergyFactor, add_comm] using
      morse_negative_endpoint_energy hB hAB
        (fun x hx => hu x (hsN hx)) (fun x hx => hv x (hsN hx))
  have hright : E e ≤ E r * Kr ∧ E r ≤ E e * Kr :=
    morse_positive_endpoint_energy hre
      (fun x hx => (morseRho_right_cap_bounds hB hAB hx.1).1)
      (fun x hx => hu x (hsR hx)) (fun x hx => hv x (hsR hx))
  have hKl : 0 ≤ Kl := morsePositiveEnergyFactor_nonneg A B j a l
  have hKn : 0 ≤ Kn := (exp_pos _).le
  have hKr : 0 ≤ Kr := morsePositiveEnergyFactor_nonneg A B j r e
  constructor
  · calc
      E e ≤ E r * Kr := hright.1
      _ ≤ (E l * Kn) * Kr := mul_le_mul_of_nonneg_right hnegative.1 hKr
      _ ≤ ((E a * Kl) * Kn) * Kr :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hleft.1 hKn) hKr
      _ = E a * morseCellEnergyFactor A B j c := by
        dsimp only [morseCellEnergyFactor, Kl, Kn, Kr, a, l, r, e]
        ring
  · calc
      E a ≤ E l * Kl := hleft.2
      _ ≤ (E r * Kn) * Kl := mul_le_mul_of_nonneg_right hnegative.2 hKl
      _ ≤ ((E e * Kr) * Kn) * Kl :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hright.2 hKn) hKl
      _ = E e * morseCellEnergyFactor A B j c := by
        dsimp only [morseCellEnergyFactor, Kl, Kn, Kr, a, l, r, e]
        ring

end ContinuousFlexibility.Radial
