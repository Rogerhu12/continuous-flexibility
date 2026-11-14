module

public import ContinuousFlexibility.Radial.SeedMorseEntrance
public import ContinuousFlexibility.Radial.CentralPhysicalTravel
public import ContinuousFlexibility.Radial.MorseParameterBridges
public import ContinuousFlexibility.Radial.MorseRealizationBasic

/-!
# Actual Morse turning components and their physical return integrals

All statements concern an arbitrary realized chain and its actual profile.
The coordinate signs, physical component, travel integral, and cell label
are derived from the realization equations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem morseRho_pos_iff_between_turns {A B x : ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) :
    0 < morseRho A B x ↔ x ∈ Ioo (morseLeftTurn A B) (morseRightTurn A B) := by
  constructor
  · intro hp
    constructor
    · rcases lt_trichotomy x (morseLeftTurn A B) with h | h | h
      · exact False.elim ((not_lt_of_ge (morseRho_neg_before_left_turn hB hAB h).le) hp)
      · have hz := (morseRho_zero_iff_turn hB hAB x).mpr (Or.inl h)
        exact False.elim (by linarith only [hz, hp])
      · exact h
    · rcases lt_trichotomy x (morseRightTurn A B) with h | h | h
      · exact h
      · have hz := (morseRho_zero_iff_turn hB hAB x).mpr (Or.inr h)
        exact False.elim (by linarith only [hz, hp])
      · exact False.elim ((not_lt_of_ge (morseRho_neg_after_right_turn hB hAB h).le) hp)
  · exact morseRho_pos_between_turns hB hAB

theorem morseRealization_profile_deriv_scaled
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (T.leftX side n) (T.rightX side n)) :
    deriv D.w (T.radius side n x) * deriv (T.radius side n) x =
      morseChainAmplitude T σ n *
        (-morseRho (morseChainA T n) (morseChainB T n) x * T.radius side n x) :=
  profile_deriv_of_cell_identity hreal.geometry.2.2.1.1
    (hreal.radius_smooth side n hn) (hreal.2.2.1 side n hn).2.1
    (fun t ht => ⟨hreal.equation side n hn t ht, hreal.profile_eq side n hn t ht⟩) x hx

theorem morseRealization_negative_at_radius_iff
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (T.leftX side n) (T.rightX side n)) :
    deriv D.w (T.radius side n x) < 0 ↔
      x ∈ Ioo (morseLeftTurn (morseChainA T n) (morseChainB T n))
        (morseRightTurn (morseChainA T n) (morseChainB T n)) := by
  have hv := hreal.derivative_positive side n hn x hx
  have hr := hreal.radius_positive side n hn x hx
  have hamp := morseChainAmplitude_pos T σ hσ n
  have hg := hreal.retained_data side n hn
  have heq := morseRealization_profile_deriv_scaled hreal side hn hx
  have hsign : deriv D.w (T.radius side n x) < 0 ↔
      deriv D.w (T.radius side n x) * deriv (T.radius side n) x < 0 := by
    constructor
    · intro h
      exact mul_neg_of_neg_of_pos h hv
    · intro h
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hn) hv.le)) h
  rw [hsign, heq]
  apply Iff.trans _ (morseRho_pos_iff_between_turns hg.1 hg.2.1)
  constructor
  · intro hneg
    by_contra h
    have hnonneg := mul_nonneg hamp.le
      (mul_nonneg (neg_nonneg.mpr (le_of_not_gt h)) hr.le)
    linarith only [hneg, hnonneg]
  · intro hp
    exact mul_neg_of_pos_of_neg hamp (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) hr)

theorem morseRealization_turns_retained
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    T.leftX side n < morseLeftTurn (morseChainA T n) (morseChainB T n) ∧
      morseLeftTurn (morseChainA T n) (morseChainB T n) <
        morseRightTurn (morseChainA T n) (morseChainB T n) ∧
      morseRightTurn (morseChainA T n) (morseChainB T n) < T.rightX side n := by
  have hg := hreal.retained_data side n hn
  refine ⟨?_, morseTurn_order hg.1 hg.2.1, hg.2.2.2.2.1⟩
  rw [hg.2.2.1]
  exact morseCellLeftCut_lt_shortLeftCapCut.trans
    (morseShortLeftCapCut_lt_leftTurn hg.1 hg.2.1)

/-- A whole retained model interval lies in its own physical seam block. -/
theorem morseRealization_model_subset_block
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (side : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    T.radius side n '' Icc (T.leftX side n) (T.rightX side n) ⊆
      morseChainBlock T side n := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := hr
  have hab := (hreal.2.2.1 side n hn).2.1
  have hmono := (hreal.radius_strictMonoOn side n hn).monotoneOn
  have hlow := hmono (left_mem_Icc.mpr hab.le) hx hx.1
  have hhigh := hmono hx (right_mem_Icc.mpr hab.le) hx.2
  have hj := hreal.join_data side n hn
  have hjoin := hj.1
  rw [hj.2.1, hj.2.2.1] at hjoin
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hjoin
    change T.radius false n x ∈
      uIcc (T.radius false n (T.rightX false n))
        (T.radius false (n + 1) (T.rightX false (n + 1)))
    rw [uIcc_of_ge ((hjoin.le.trans hlow).trans hhigh)]
    exact ⟨hjoin.le.trans hlow, hhigh⟩
  | true =>
    simp only [↓reduceIte] at hjoin
    change T.radius true n x ∈
      uIcc (T.radius true n (T.leftX true n))
        (T.radius true (n + 1) (T.leftX true (n + 1)))
    rw [uIcc_of_le ((hlow.trans hhigh).trans hjoin.le)]
    exact ⟨hlow, hhigh.trans hjoin.le⟩

/-- Every genuine model turning interval is one complete negative
component, has its computed physical travel, and is pointwise covered
by cells of precisely the model index. -/
theorem morseRealization_model_return
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) :
    let A := morseChainA T n
    let B := morseChainB T n
    let l := T.radius side n (morseLeftTurn A B)
    let h := T.radius side n (morseRightTurn A B)
    NegativeRadialComponent D l h ∧
      radialTravel D l h = Real.pi / (2 * sqrt (T.d n : ℝ)) ∧
      ∀ r ∈ Ioo l h, ∃ m, D.cellIndex m = n ∧ r ∈ D.cells m := by
  let A := morseChainA T n
  let B := morseChainB T n
  let R := T.radius side n
  let a := morseLeftTurn A B
  let b := morseRightTurn A B
  change NegativeRadialComponent D (R a) (R b) ∧
    radialTravel D (R a) (R b) = Real.pi / (2 * sqrt (T.d n : ℝ)) ∧ _
  obtain ⟨hleft, hab, hright⟩ := morseRealization_turns_retained hreal side hn
  have huIcc : uIcc a b = Icc a b := uIcc_of_le (show a ≤ b from hab.le)
  have hsub : Icc a b ⊆ Icc (T.leftX side n) (T.rightX side n) :=
    Icc_subset_Icc hleft.le hright.le
  have ha := hsub (left_mem_Icc.mpr hab.le)
  have hb := hsub (right_mem_Icc.mpr hab.le)
  have hR := hreal.radius_smooth side n hn
  have hmono := (hreal.radius_strictMonoOn side n hn).mono hsub
  have himage : R '' Ioo a b = Ioo (R a) (R b) :=
    hR.continuous.continuousOn.image_Ioo_of_strictMonoOn hab.le hmono
  have hge := hreal.retained_data side n hn
  have hamp := morseChainAmplitude_pos T σ hσ n
  have hzero (x : ℝ) (hx : x ∈ Icc (T.leftX side n) (T.rightX side n))
      (hρ : morseRho A B x = 0) : deriv D.w (R x) = 0 := by
    have he := morseRealization_profile_deriv_scaled hreal side hn hx
    change deriv D.w (R x) * deriv R x =
      morseChainAmplitude T σ n * (-morseRho A B x * R x) at he
    rw [hρ, neg_zero, zero_mul, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (hreal.derivative_positive side n hn x hx).ne'
  have hneg : NegativeRadialComponent D (R a) (R b) := by
    refine ⟨(hreal.radius_mem_core side n hn a ha).1,
      hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab,
      (hreal.radius_mem_core side n hn b hb).2,
      hzero a ha ((morseRho_zero_iff_turn hge.1 hge.2.1 a).mpr (Or.inl rfl)),
      hzero b hb ((morseRho_zero_iff_turn hge.1 hge.2.1 b).mpr (Or.inr rfl)), ?_⟩
    intro r hr
    have hrim : r ∈ R '' Ioo a b := by rwa [himage]
    obtain ⟨x, hx, rfl⟩ := hrim
    exact (morseRealization_negative_at_radius_iff hreal hσ side hn
      (hsub (Ioo_subset_Icc_self hx))).mpr hx
  have hDensity (x : ℝ) (hx : x ∈ uIcc a b) :
      -(deriv D.w (R x)) / (R x * D.w (R x)) =
        morseRho A B x / (deriv R x) ^ 2 := by
    have hx' : x ∈ Icc (T.leftX side n) (T.rightX side n) :=
      hsub (by simpa only [huIcc] using hx)
    have hr : R x ≠ 0 := (hreal.radius_positive side n hn x hx').ne'
    have hv : deriv R x ≠ 0 := (hreal.derivative_positive side n hn x hx').ne'
    have hw : D.w (R x) = morseChainAmplitude T σ n * deriv R x :=
      hreal.profile_eq side n hn x hx'
    have hd : deriv D.w (R x) * deriv R x =
        morseChainAmplitude T σ n * (-morseRho A B x * R x) :=
      morseRealization_profile_deriv_scaled hreal side hn hx'
    have hdv := congrArg (fun z : ℝ => z * deriv R x) hd
    rw [hw]
    field_simp [hamp.ne', hr, hv] <;> nlinarith only [hd, hdv]
  have hcontinuity : ContinuousOn
      (fun r => sqrt (-(deriv D.w r) / (r * D.w r))) (R '' uIcc a b) := by
    have hw := hreal.geometry.2.2.1.1
    have hwd := (contDiff_infty_iff_deriv.mp hw).2.continuous
    intro r hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hx' : x ∈ Icc (T.leftX side n) (T.rightX side n) :=
      hsub (by simpa only [huIcc] using hx)
    have hrp := hreal.radius_positive side n hn x hx'
    have hwp := hreal.geometry.2.2.2.2.1 _ (hreal.radius_mem_core side n hn x hx')
    exact ((hwd.continuousAt.neg.div (continuousAt_id.mul hw.continuous.continuousAt)
      (mul_ne_zero hrp.ne' hwp.ne')).sqrt).continuousWithinAt
  have htravel : radialTravel D (R a) (R b) = morseTravel A B :=
    opticalTravel_integral_of_pullback
      (fun x _ => (hR.differentiable (by simp) x).hasDerivAt)
      ((contDiff_infty_iff_deriv.mp hR).2.continuous.continuousOn)
      (fun x hx => hreal.derivative_positive side n hn x
        (hsub (by simpa only [huIcc] using hx)))
      hDensity hcontinuity
  have hd : 1 < T.d n := by
    rw [hreal.d_eq n hn]
    exact morseChainInteger_ge_two n
  have hparameter := (morseParameter_return_and_level_gaps hd (hreal.1 n hn).2.1).2.2.1
  refine ⟨hneg, htravel.trans hparameter, ?_⟩
  intro r hr
  have hrim : r ∈ R '' Ioo a b := by rwa [himage]
  obtain ⟨x, hx, rfl⟩ := hrim
  exact hreal.2.2.2.2.2.2.2.2.1 side n hn _
    (morseRealization_model_subset_block hreal side hn
      ⟨x, hsub (Ioo_subset_Icc_self hx), rfl⟩)

end ContinuousFlexibility.Radial
