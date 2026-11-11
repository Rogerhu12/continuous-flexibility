import ContinuousFlexibility.Radial.OuterCoreMassScale
import ContinuousFlexibility.Radial.MorseTransitionBands
import ContinuousFlexibility.Radial.MorseRetainedRadiusModelBounds

/-!
# The actual first mass in the normalized radial gauge

The density used by the deep equation is g²w/r in logarithmic radius.
Dividing its first mass by the squared entrance gauge leaves the radial
integral below. On an actual mass interval the radius is within O(A)
of its right turning radius. Hence j²A ≤ 1 controls this normalized
density uniformly, including a left entrance in the preceding gap.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The first-mass expression after division by the entrance gauge. -/
def normalizedRadialGaugeMass (D : ReferenceData) (j : ℕ)
    (entrance l r : ℝ) : ℝ :=
  ∫ x in l..r, (x / entrance) ^ (2 * j ^ 2) * D.w x / x ^ 2

/-- A bounded gauge factor converts the actual Hilbert density to the
moment density already controlled by the Morse-cell construction. -/
theorem normalizedRadialGaugeMass_le_moment {D : ReferenceData}
    (hD : RadialProfileGeometry D) (j : ℕ) {entrance l r G : ℝ}
    (hlr : l ≤ r) (hsub : Icc l r ⊆ radialCore D) (hG : 0 ≤ G)
    (hgauge : ∀ x ∈ Icc l r, (x / entrance) ^ (2 * j ^ 2) ≤ G) :
    normalizedRadialGaugeMass D j entrance l r ≤
      (G / D.a ^ 8) * (∫ x in l..r, D.w x * x ^ 6) := by
  have hw : Continuous D.w := hD.2.2.1.1.continuous
  have hx₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := hD.1.trans (hsub hx).1
  have hw₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ D.w x :=
    (hD.2.2.2.2.1 x (hsub hx)).le
  have hpoint (x : ℝ) (hx : x ∈ Icc l r) :
      (x / entrance) ^ (2 * j ^ 2) * D.w x / x ^ 2 ≤
        (G / D.a ^ 8) * (D.w x * x ^ 6) := by
    have hp : D.a ^ 8 ≤ x ^ 8 :=
      pow_le_pow_left₀ hD.1.le (hsub hx).1.le 8
    have hratio : (1 : ℝ) / x ^ 2 ≤ x ^ 6 / D.a ^ 8 := by
      apply (div_le_div_iff₀ (pow_pos (hx₀ x hx) 2) (pow_pos hD.1 8)).mpr
      calc
        1 * D.a ^ 8 = D.a ^ 8 := one_mul _
        _ ≤ x ^ 8 := hp
        _ = x ^ 6 * x ^ 2 := by ring
    calc
      _ = ((x / entrance) ^ (2 * j ^ 2) * D.w x) * (1 / x ^ 2) := by ring
      _ ≤ (G * D.w x) * (x ^ 6 / D.a ^ 8) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hgauge x hx) (hw₀ x hx)) hratio
          (by positivity) (mul_nonneg hG (hw₀ x hx))
      _ = _ := by ring
  have hleft : ContinuousOn
      (fun x => (x / entrance) ^ (2 * j ^ 2) * D.w x / x ^ 2) (Icc l r) :=
    (((continuous_id.div_const entrance).pow (2 * j ^ 2)).mul hw).continuousOn.div
      (continuousOn_id.pow 2) (fun x hx => (pow_pos (hx₀ x hx) 2).ne')
  have hright : Continuous (fun x : ℝ => (G / D.a ^ 8) * (D.w x * x ^ 6)) :=
    continuous_const.mul (hw.mul (continuous_id.pow 6))
  calc
    _ ≤ ∫ x in l..r, (G / D.a ^ 8) * (D.w x * x ^ 6) :=
      intervalIntegral.integral_mono_on hlr
        (hleft.intervalIntegrable_of_Icc hlr) (hright.intervalIntegrable l r) hpoint
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The normalized actual radius at the left end of a mass interval
is close to its right turning radius, uniformly in the height choice. -/
theorem morseRealized_mass_radius_lower {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (h100 : 100 ≤ n) :
    let s := morseChainMassEnd T side n
    let l := T.radius side n (T.leftX side n)
    s / 2 ≤ l ∧ s - l ≤ 6 * morseChainA T n * s := by
  let A := morseChainA T n
  let B := morseChainB T n
  let R := T.radius side n
  let s := morseChainMassEnd T side n
  let r : ℝ → ℝ := fun x => R x / s
  obtain ⟨hB, hAB, hleft, hab, hbe, _, hspeed⟩ := h.retained_data side n hn
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have ha : T.leftX side n = morseCellLeftCut := hleft
  have hb : morseChainRightTurn T n = morseRightTurn A B := rfl
  have hd1 : 1 ≤ (T.d n : ℝ) :=
    (one_le_exp_iff.mpr (sq_nonneg (n : ℝ))).trans (h.1 n hn).1
  have hBA := morseChainB_A_bounds T n hd1
  have hA₀ : A ≤ 1 / 1000 := by
    apply morseChainA_le_of_sq_ge_log T n (h.d_eq n hn) (by norm_num)
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast h100
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hnR 2
    have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / (1 / 1000 : ℝ))
    norm_num at hsq hlog ⊢
    linarith only [hlog, hsq]
  have hs : 0 < s := h.radius_positive side n hn _ ⟨hab.le, hbe.le⟩
  have hR : ContDiff ℝ ∞ R := h.radius_smooth side n hn
  have hr : ContDiff ℝ ∞ r := hR.div_const s
  have hd (x : ℝ) : deriv r x = deriv R x / s :=
    (((hR.differentiable (by simp) x).hasDerivAt).div_const s).deriv
  have hdd (x : ℝ) : deriv (deriv r) x = deriv (deriv R) x / s := by
    have he : deriv r = fun y => deriv R y / s := funext hd
    rw [he]
    exact ((((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x).hasDerivAt).div_const s).deriv
  have hrb : r (morseRightTurn A B) = 1 := by
    change s / s = 1
    exact div_self hs.ne'
  have hvb : deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 := by
    rw [hd]
    change deriv (T.radius side n) (morseChainRightTurn T n) / s = _
    rw [hspeed, mul_div_cancel_right₀ _ hs.ne']
  have hEq (x : ℝ) (hx : x ∈ Icc morseCellLeftCut (morseRightTurn A B)) :
      deriv (deriv r) x = -morseRho A B x * r x := by
    have hsub : x ∈ Icc (T.leftX side n) (T.rightX side n) := by
      rw [ha]
      exact ⟨hx.1, hx.2.trans hbe.le⟩
    rw [hdd, h.equation side n hn x hsub]
    dsimp only [r]
    ring
  have hclose := (morseLeftCap_radius_bounds hB hAB hA₀ hBA.1 hBA.2 hr hrb hvb hEq).1
    morseCellLeftCut (left_mem_Icc.mpr (morseCellLeftCut_lt_rightTurn hB hAB).le)
  have hnormalized : 1 - 6 * A ≤ T.radius side n (T.leftX side n) / s := by
    rw [ha]
    change 1 - 6 * A ≤ r morseCellLeftCut
    linarith only [(abs_le.mp hclose.1).1]
  have hlower := (le_div_iff₀ hs).mp hnormalized
  change s / 2 ≤ T.radius side n (T.leftX side n) ∧
    s - T.radius side n (T.leftX side n) ≤ 6 * A * s
  constructor
  · have hhalf : (1 / 2 : ℝ) ≤ 1 - 6 * A := by linarith only [hA₀]
    have hh := mul_le_mul_of_nonneg_right hhalf hs.le
    nlinarith only [hh, hlower]
  · linarith only [hlower]

/-- The entrance may be at the left mass endpoint or at any larger
radius, as happens for a left tail with an initial resistance edge. -/
theorem radialGauge_mass_interval_power_le {A s l entrance x : ℝ} (j : ℕ)
    (hA : 0 ≤ A) (hs : 0 < s) (hl : s / 2 ≤ l)
    (hwidth : s - l ≤ 6 * A * s) (hentry : l ≤ entrance)
    (hx : x ∈ Icc l s) (hfrequency : (j : ℝ) ^ 2 * A ≤ 1) :
    (x / entrance) ^ (2 * j ^ 2) ≤ exp 24 := by
  have hlpos : 0 < l := (by linarith only [hs] : 0 < s / 2).trans_le hl
  have hepos : 0 < entrance := hlpos.trans_le hentry
  have hxpos : 0 < x := hlpos.trans_le hx.1
  have hAl := mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hA)
  have hdiv : s / l ≤ 1 + 12 * A := by
    apply (div_le_iff₀ hlpos).mpr
    nlinarith only [hAl, hwidth]
  have hratio : x / entrance ≤ 1 + 12 * A := calc
    _ ≤ x / l := div_le_div_of_nonneg_left hxpos.le hlpos hentry
    _ ≤ s / l := div_le_div_of_nonneg_right hx.2 hlpos.le
    _ ≤ _ := hdiv
  have hlog : log (x / entrance) ≤ 12 * A := by
    have hh := log_le_sub_one_of_pos (div_pos hxpos hepos)
    linarith only [hh, hratio]
  have hlogmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (j : ℝ)))
  calc
    _ = exp (((2 * j ^ 2 : ℕ) : ℝ) * log (x / entrance)) := by
      rw [exp_nat_mul, exp_log (div_pos hxpos hepos)]
    _ ≤ exp 24 := by
      apply exp_le_exp.mpr
      push_cast
      nlinarith only [hlogmul, hfrequency]

/-- A physical mass interval has the required normalized first-mass
scale, derived from the actual profile and actual cell radius. -/
theorem morseRealized_normalized_mass_le {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K)
    (side : Bool) (n : ℕ) (hn : T.index ≤ n) (h100 : 100 ≤ n)
    (j : ℕ) (hfrequency : (j : ℝ) ^ 2 * morseChainA T n ≤ 1)
    {entrance : ℝ} (hentry : T.radius side n (T.leftX side n) ≤ entrance) :
    normalizedRadialGaugeMass D j entrance (T.radius side n (T.leftX side n))
        (morseChainMassEnd T side n) ≤
      (exp 24 / D.a ^ 8) * morseChainAmplitude T σ n * K * morseChainA T n ^ 2 := by
  let l := T.radius side n (T.leftX side n)
  let s := morseChainMassEnd T side n
  obtain ⟨hB, hAB, _, hlt, htr, _, _⟩ := h.retained_data side n hn
  have hA : 0 < morseChainA T n := (mul_pos (by norm_num) hB).trans hAB
  have hs : 0 < s := h.radius_positive side n hn _ ⟨hlt.le, htr.le⟩
  have hlcore : l ∈ radialCore D := h.radius_mem_core side n hn _
    (left_mem_Icc.mpr (hlt.trans htr).le)
  have hscore : s ∈ radialCore D := h.radius_mem_core side n hn _ ⟨hlt.le, htr.le⟩
  have hls : l ≤ s := (h.radius_strictMonoOn side n hn).monotoneOn
    (left_mem_Icc.mpr (hlt.trans htr).le) ⟨hlt.le, htr.le⟩ hlt.le
  have hsub : Icc l s ⊆ radialCore D := fun _ hx =>
    ⟨hlcore.1.trans_le hx.1, hx.2.trans_lt hscore.2⟩
  have hradius := morseRealized_mass_radius_lower h side n hn h100
  have hgauge (x : ℝ) (hx : x ∈ Icc l s) :
      (x / entrance) ^ (2 * j ^ 2) ≤ exp 24 :=
    radialGauge_mass_interval_power_le j hA.le hs hradius.1 hradius.2 hentry hx hfrequency
  have hmoment : morseCellMass T D side n ≤
      morseChainAmplitude T σ n * (K * morseChainA T n ^ 2) := by
    rw [(morseRealized_model_integrals h hσ side n hn).1]
    exact mul_le_mul_of_nonneg_left (hcell.mass_upper side n hn)
      (morseChainAmplitude_pos T σ hσ n).le
  calc
    _ ≤ (exp 24 / D.a ^ 8) * morseCellMass T D side n :=
      normalizedRadialGaugeMass_le_moment h.geometry j hls hsub (exp_pos _).le hgauge
    _ ≤ (exp 24 / D.a ^ 8) *
        (morseChainAmplitude T σ n * (K * morseChainA T n ^ 2)) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by ring

/-- The already-proved frequency bands make the gauge uniformly small
on every cell after the transition cell. -/
theorem morseTransition_eventually_gauge_small {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (h : MorseChainRealization T σ D C)
    {Cstar : ℝ} (hCstar : 0 < Cstar) :
    ∀ᶠ n : ℕ in atTop, ∀ j, radialFrequencyBand T Cstar n j → ∀ m, n < m →
      (j : ℝ) ^ 2 * morseChainA T m ≤ 1 := by
  have hsqrt : 0 < sqrt (log 4) := sqrt_pos.mpr (log_pos (by norm_num))
  filter_upwards [morseTransition_eventually_deep T hCstar
    (fun k hk => h.d_eq k hk) hsqrt] with n hn
  intro j hj m hm
  have hidx : T.index ≤ m := hj.1.trans hm.le
  obtain ⟨hB, hAB, _⟩ := h.retained_data true m hidx
  have hA : 0 < morseChainA T m := (mul_pos (by norm_num) hB).trans hAB
  have hratio : (4 : ℝ) ≤ morseChainA T m / morseChainB T m := by
    exact ((le_div_iff₀ hB).mpr hAB.le)
  have hsqrtle : sqrt (log 4) ≤ sqrt (log (morseChainA T m / morseChainB T m)) :=
    sqrt_le_sqrt (log_le_log (by norm_num) hratio)
  have hmul := mul_le_mul_of_nonneg_left hsqrtle
    (mul_nonneg (sq_nonneg (j : ℝ)) hA.le)
  have hlt := hmul.trans_lt (hn j hj m hm)
  have hlast : (j : ℝ) ^ 2 * morseChainA T m < 1 := by
    apply (mul_lt_mul_right hsqrt).mp
    simpa only [one_mul] using hlt
  exact hlast.le


/-- The first cell after the transition has the preceding height scale,
with an explicit frequency-independent coefficient. -/
theorem morseRealized_next_normalized_mass_le_height_exp
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {K : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (side : Bool) (n : ℕ)
    (hn : T.index ≤ n) (h100 : 100 ≤ n) (j : ℕ)
    (hfrequency : (j : ℝ) ^ 2 * morseChainA T (n + 1) ≤ 1)
    {entrance : ℝ}
    (hentry : T.radius side (n + 1) (T.leftX side (n + 1)) ≤ entrance) :
    normalizedRadialGaugeMass D j entrance
        (T.radius side (n + 1) (T.leftX side (n + 1)))
        (morseChainMassEnd T side (n + 1)) ≤
      (exp 24 / D.a ^ 8 * K * 81) *
        morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := by
  have hn₁ : T.index ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hApos : 0 ≤ morseChainA T (n + 1) := by
    obtain ⟨hB, hAB, _⟩ := h.retained_data side (n + 1) hn₁
    exact ((mul_pos (by norm_num) hB).trans hAB).le
  have hA := morseChainA_le_nine T (n + 1) (h.d_eq (n + 1) hn₁)
  have hA₂ : morseChainA T (n + 1) ^ 2 ≤ 81 := by
    simpa only [show (9 : ℝ) ^ 2 = 81 by norm_num] using pow_le_pow_left₀ hApos hA 2
  have hamp := morseAdjacentScale_amplitude_le_exp_sq T σ hσ
    (by omega : 1 ≤ n) hn hn₁ (Or.inl rfl)
  have hcoef : 0 ≤ exp 24 / D.a ^ 8 * K := by
    exact mul_nonneg (by positivity) hcell.pos.le
  calc
    _ ≤ (exp 24 / D.a ^ 8) * morseChainAmplitude T σ (n + 1) *
        K * morseChainA T (n + 1) ^ 2 :=
      morseRealized_normalized_mass_le h hσ hcell side (n + 1) hn₁
        (by omega) j hfrequency hentry
    _ = (exp 24 / D.a ^ 8 * K) *
        (morseChainAmplitude T σ (n + 1) * morseChainA T (n + 1) ^ 2) := by ring
    _ ≤ (exp 24 / D.a ^ 8 * K) *
        ((morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2)) * 81) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hamp hA₂ (sq_nonneg _)
          (mul_nonneg (morseChainAmplitude_pos T σ hσ n).le (exp_pos _).le)) hcoef
    _ = _ := by ring

/-- Uniformly in the frequency band, both actual first mass intervals
have the manuscript's height scale after entrance normalization. -/
theorem morseRealized_next_normalized_mass_eventually_le
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ} {K Cstar : ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hcell : MorseRealizedCellEstimates T K) (hCstar : 0 < Cstar) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
      ∀ᶠ n : ℕ in atTop, ∀ j, radialFrequencyBand T Cstar n j →
        ∀ side : Bool, ∀ entrance : ℝ,
          T.radius side (n + 1) (T.leftX side (n + 1)) ≤ entrance →
          normalizedRadialGaugeMass D j entrance
              (T.radius side (n + 1) (T.leftX side (n + 1)))
              (morseChainMassEnd T side (n + 1)) ≤
            morseChainAmplitude T σ n * exp (Cbound * (n : ℝ) ^ 2) := by
  let M := exp 24 / D.a ^ 8 * K * 81
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (by positivity) hcell.pos.le) (by norm_num)
  refine ⟨27 + M, by linarith only [hM], ?_⟩
  filter_upwards [morseTransition_eventually_gauge_small h hCstar,
    eventually_ge_atTop (100 : ℕ)] with n hfreq h100
  intro j hj side entrance hentry
  have hbound := morseRealized_next_normalized_mass_le_height_exp
    h hσ hcell side n hj.1 h100 j (hfreq j hj (n + 1) (Nat.lt_succ_self n)) hentry
  have hpref := nonneg_le_exp_mul_nat_sq hM (by omega : 1 ≤ n)
  calc
    _ ≤ M * morseChainAmplitude T σ n * exp (27 * (n : ℝ) ^ 2) := hbound
    _ ≤ (exp (M * (n : ℝ) ^ 2) * morseChainAmplitude T σ n) *
        exp (27 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (morseChainAmplitude_pos T σ hσ n).le)
        (exp_pos _).le
    _ = morseChainAmplitude T σ n * exp ((27 + M) * (n : ℝ) ^ 2) := by
      rw [mul_comm (exp (M * (n : ℝ) ^ 2)) (morseChainAmplitude T σ n),
        mul_assoc, ← exp_add]
      congr 2
      ring

end ContinuousFlexibility.Radial
