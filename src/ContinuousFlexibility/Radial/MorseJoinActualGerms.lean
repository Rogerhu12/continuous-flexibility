module

public import ContinuousFlexibility.Radial.MorseCellJoinCollars
public import ContinuousFlexibility.Radial.MorsePositiveJoin

/-!
# Actual Morse collar germs at a positive join

The local physical logarithmic height is smooth on the image of its
model interval. A compact cutoff globalizes it while preserving its
full germ at every point of the closed interval used by the join.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A compact interval strictly inside a smooth interval admits a
globally smooth compactly supported extension of the whole germ. -/
theorem exists_contDiff_joinGerm_extension {u v a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hbv : b < v) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo u v)) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ x ∈ Icc a b, F =ᶠ[𝓝 x] f := by
  let m : ℝ := (a + b) / 2
  let d : ℝ := (b - a) / 2
  let ε : ℝ := min (a - u) (v - b) / 3
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr hua) (sub_pos.mpr hbv)) (by norm_num)
  have hεL : 2 * ε < a - u := by
    have h := min_le_left (a - u) (v - b)
    dsimp only [ε]
    linarith only [h, hua]
  have hεR : 2 * ε < v - b := by
    have h := min_le_right (a - u) (v - b)
    dsimp only [ε]
    linarith only [h, hbv]
  let χ : ContDiffBump m :=
    ⟨d + ε, d + 2 * ε, by dsimp only [d]; linarith only [hab, hε], by linarith only [hε]⟩
  let F : ℝ → ℝ := fun x => χ x * f x
  have hsupp : tsupport (χ : ℝ → ℝ) ⊆ Ioo u v := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
    intro x hx
    change m - (d + 2 * ε) ≤ x ∧ x ≤ m + (d + 2 * ε) at hx
    change u < x ∧ x < v
    dsimp only [m, d] at hx
    exact ⟨by linarith only [hx.1, hεL], by linarith only [hx.2, hεR]⟩
  have hFc : HasCompactSupport F := by
    change HasCompactSupport ((χ : ℝ → ℝ) * f)
    exact χ.hasCompactSupport.mul_right
  refine ⟨F, contDiff_iff_contDiffAt.mpr ?_, hFc, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport (χ : ℝ → ℝ)
    · exact χ.contDiffAt.mul (hf.contDiffAt (isOpen_Ioo.mem_nhds (hsupp hx)))
    · have hχ := notMem_tsupport_iff_eventuallyEq.mp hx
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [hχ] with y hy
      change χ y = 0 at hy
      change χ y * f y = 0
      rw [hy, zero_mul]
  · intro x hx
    have hi : x ∈ Metric.ball m χ.rIn := by
      rw [Real.ball_eq_Ioo]
      change m - (d + ε) < x ∧ x < m + (d + ε)
      dsimp only [m, d]
      exact ⟨by linarith only [hx.1, hε], by linarith only [hx.2, hε]⟩
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hi] with y hy
    change χ y = 1 at hy
    change χ y * f y = f y
    rw [hy, one_mul]

private theorem morseCollar_scaledRadius_strictMonoOn {s a b : ℝ} {r : ℝ → ℝ}
    (hs : 0 < s) (hr : ContDiff ℝ ∞ r) (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) :
    StrictMonoOn (fun x => s * r x) (Icc a b) := by
  have hcont : Continuous (fun x => s * r x) := continuous_const.mul hr.continuous
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcont.continuousOn
  intro x hx
  have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
  have hd : HasDerivAt (fun x => s * r x) (s * deriv r x) x :=
    ((hr.differentiable (by simp) x).hasDerivAt).const_mul s
  rw [hd.deriv]
  exact mul_pos hs (hv x hx')

theorem morseCollar_scaledRadius_image_Ioo {s a b : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) :
    (fun x => s * r x) '' Ioo a b = Ioo (s * r a) (s * r b) := by
  have hcont : Continuous (fun x => s * r x) := continuous_const.mul hr.continuous
  exact ContinuousOn.image_Ioo_of_strictMonoOn hab hcont.continuousOn
    (morseCollar_scaledRadius_strictMonoOn hs hr hv)

theorem morseCollarLogProfile_at_model {lam s a b x : ℝ} {r : ℝ → ℝ}
    (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b) :
    morseCollarLogProfile r lam s a b (s * r x) = log (lam * s * deriv r x) := by
  have hmono : StrictMonoOn (fun x => s * r x) (Ioo a b) :=
    (morseCollar_scaledRadius_strictMonoOn hs hr hv).mono Ioo_subset_Icc_self
  have hleft : LeftInvOn (morseCollarCoordinate r s a b) (fun x => s * r x) (Ioo a b) :=
    hmono.injOn.leftInvOn_invFunOn
  unfold morseCollarLogProfile
  rw [hleft hx]

theorem exp_morseCollarLogProfile_eqOn {lam s a b : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hLam : 0 < lam) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) :
    EqOn (fun y => exp (morseCollarLogProfile r lam s a b y))
      (fun y => lam * s * deriv r (morseCollarCoordinate r s a b y)) (Ioo (s * r a) (s * r b)) := by
  intro y hy
  rw [← morseCollar_scaledRadius_image_Ioo hab hs hr hv] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hmono : StrictMonoOn (fun t => s * r t) (Ioo a b) :=
    (morseCollar_scaledRadius_strictMonoOn hs hr hv).mono Ioo_subset_Icc_self
  have hleft : LeftInvOn (morseCollarCoordinate r s a b) (fun t => s * r t) (Ioo a b) :=
    hmono.injOn.leftInvOn_invFunOn
  have hp : 0 < lam * s * deriv r (morseCollarCoordinate r s a b (s * r x)) := by
    rw [hleft hx]
    exact mul_pos (mul_pos hLam hs) (hv x hx)
  exact exp_log hp

theorem contDiffOn_morseCollarLogProfile {A B lam s a b : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hLam : 0 < lam) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t)
    (hEq : ∀ t ∈ Ioo a b, deriv (deriv r) t = -morseRho A B t * r t) :
    ContDiffOn ℝ ∞ (morseCollarLogProfile r lam s a b) (Ioo (s * r a) (s * r b)) := by
  intro y hy
  rw [← morseCollar_scaledRadius_image_Ioo hab hs hr hv] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (morseCollarLogProfile_jet hLam hs hr hv hx (hEq x hx)).2.1.contDiffWithinAt

/-- The extension preserves the genuine physical derivative of the
model logarithmic height on the entire support collar. -/
theorem exists_morseCollarLogProfile_extension {A B lam s a b p q : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hLam : 0 < lam) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t)
    (hEq : ∀ t ∈ Ioo a b, deriv (deriv r) t = -morseRho A B t * r t)
    (hp : s * r a < p) (hpq : p ≤ q) (hq : q < s * r b) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∀ y ∈ Icc p q, F =ᶠ[𝓝 y] morseCollarLogProfile r lam s a b) ∧
      ∀ x ∈ Ioo a b, s * r x ∈ Icc p q →
        HasDerivAt F (-morseRho A B x * r x / (s * (deriv r x) ^ 2)) (s * r x) := by
  obtain ⟨F, hFs, hFc, hFg⟩ := exists_contDiff_joinGerm_extension hp hpq hq
    (contDiffOn_morseCollarLogProfile hab hLam hs hr hv hEq)
  refine ⟨F, hFs, hFc, hFg, ?_⟩
  intro x hx hy
  exact (morseCollarLogProfile_jet hLam hs hr hv hx (hEq x hx)).2.2.congr_of_eventuallyEq (hFg _ hy)

/-- Only the values and derivatives on the two supported collars enter
the actual integral budget. -/
theorem morseJoinBudget_congr_of_germs {a b hL hR m : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hab : a ≤ b) (hhL : 0 < hL) (hhR : 0 < hR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR) :
    MorseJoinBudget a b hL hR m FL FR ↔ MorseJoinBudget a b hL hR m fL fR := by
  have hLi : (∫ x in a..b, morseJoinLeftSlope a hL FL x) =
      ∫ x in a..b, morseJoinLeftSlope a hL fL x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    by_cases hx' : x ≤ a + hL
    · simp only [morseJoinLeftSlope, (hLg x ⟨hx.1, hx'⟩).deriv_eq]
    · simp only [morseJoinLeftSlope,
        morseJoinLeftWeight_zero hhL (le_of_lt (lt_of_not_ge hx')), zero_mul]
  have hRi : (∫ x in a..b, morseJoinRightSlope b hR FR x) =
      ∫ x in a..b, morseJoinRightSlope b hR fR x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    by_cases hx' : b - hR ≤ x
    · simp only [morseJoinRightSlope, (hRg x ⟨hx', hx.2⟩).deriv_eq]
    · simp only [morseJoinRightSlope,
        morseJoinRightWeight_zero hhR (le_of_lt (lt_of_not_ge hx')), zero_mul]
  have hLa : FL a = fL a :=
    (hLg a ⟨le_rfl, le_add_of_nonneg_right hhL.le⟩).eq_of_nhds
  have hRb : FR b = fR b :=
    (hRg b ⟨sub_le_self _ hhR.le, le_rfl⟩).eq_of_nhds
  unfold MorseJoinBudget
  rw [hLi, hRi, hLa, hRb]

/-- Bind two genuine model profiles to the same positive-join formula.
The slope hypotheses use the model ODE expression on the indicated
physical support collars. The budget uses the original local profiles. -/
theorem exists_morseJoin_of_model_germs
    {AL BL AR BR lamL lamR sL sR pL qL pR qR xL xR hL hR m : ℝ}
    {rL rR : ℝ → ℝ}
    (hLamL : 0 < lamL) (hsL : 0 < sL) (hrL : ContDiff ℝ ∞ rL)
    (hvL : ∀ t ∈ Ioo pL qL, 0 < deriv rL t)
    (hEqL : ∀ t ∈ Ioo pL qL, deriv (deriv rL) t = -morseRho AL BL t * rL t)
    (hxL : xL ∈ Ioo pL qL)
    (hLamR : 0 < lamR) (hsR : 0 < sR) (hrR : ContDiff ℝ ∞ rR)
    (hvR : ∀ t ∈ Ioo pR qR, 0 < deriv rR t)
    (hEqR : ∀ t ∈ Ioo pR qR, deriv (deriv rR) t = -morseRho AR BR t * rR t)
    (hxR : xR ∈ Ioo pR qR)
    (hhL : 0 < hL) (hhR : 0 < hR)
    (hLin : sL * rL xL + hL < sL * rL qL)
    (hRin : sR * rR pR < sR * rR xR - hR)
    (hsep : sL * rL xL + hL < sR * rR xR - hR)
    (hm : 0 ≤ m)
    (hFloorL : ∀ t ∈ Ioo pL qL, sL * rL t ∈ Icc (sL * rL xL) (sL * rL xL + hL) →
      m ≤ -morseRho AL BL t * rL t / (sL * (deriv rL t) ^ 2))
    (hFloorR : ∀ t ∈ Ioo pR qR, sR * rR t ∈ Icc (sR * rR xR - hR) (sR * rR xR) →
      m ≤ -morseRho AR BR t * rR t / (sR * (deriv rR t) ^ 2))
    (hbudget : MorseJoinBudget (sL * rL xL) (sR * rR xR) hL hR m
      (morseCollarLogProfile rL lamL sL pL qL) (morseCollarLogProfile rR lamR sR pR qR)) :
    let a := sL * rL xL
    let b := sR * rR xR
    let fL := morseCollarLogProfile rL lamL sL pL qL
    let fR := morseCollarLogProfile rR lamR sR pR qR
    ∃ FL FR : ℝ → ℝ, ContDiff ℝ ∞ FL ∧ ContDiff ℝ ∞ FR ∧
      HasCompactSupport FL ∧ HasCompactSupport FR ∧
      (∀ y ∈ Icc a (a + hL), FL =ᶠ[𝓝 y] fL) ∧
      (∀ y ∈ Icc (b - hR) b, FR =ᶠ[𝓝 y] fR) ∧
      MorseJoinBudget a b hL hR m FL FR ∧
      let F := morseJoinLog a b hL hR FL FR
      let w := morseJoinProfile a b hL hR FL FR
      ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ w ∧
      (F =ᶠ[𝓝 a] fL) ∧ (F =ᶠ[𝓝 b] fR) ∧
      (w =ᶠ[𝓝 a] fun y => lamL * sL * deriv rL (morseCollarCoordinate rL sL pL qL y)) ∧
      (w =ᶠ[𝓝 b] fun y => lamR * sR * deriv rR (morseCollarCoordinate rR sR pR qR y)) ∧
      (∀ y ∈ Icc a b, m ≤ deriv F y ∧ m * w y ≤ deriv w y) ∧
      (∀ y ∈ Icc (a + hL) (b - hR), deriv F y = morseJoinConstant a b hL hR FL FR) ∧
      (∀ y, 0 < w y) ∧ MonotoneOn w (Icc a b) ∧ (0 < m → StrictMonoOn w (Icc a b)) := by
  dsimp only
  let a := sL * rL xL
  let b := sR * rR xR
  let fL := morseCollarLogProfile rL lamL sL pL qL
  let fR := morseCollarLogProfile rR lamR sR pR qR
  have hpqL : pL ≤ qL := (hxL.1.trans hxL.2).le
  have hpqR : pR ≤ qR := (hxR.1.trans hxR.2).le
  have hmonoL := morseCollar_scaledRadius_strictMonoOn hsL hrL hvL
  have hmonoR := morseCollar_scaledRadius_strictMonoOn hsR hrR hvR
  have hLlo : sL * rL pL < a :=
    hmonoL (left_mem_Icc.mpr hpqL) (Ioo_subset_Icc_self hxL) hxL.1
  have hRhi : b < sR * rR qR :=
    hmonoR (Ioo_subset_Icc_self hxR) (right_mem_Icc.mpr hpqR) hxR.2
  obtain ⟨FL, hFL, hFLc, hFLg, hFLd⟩ := exists_morseCollarLogProfile_extension
    (p := a) (q := a + hL) hpqL hLamL hsL hrL hvL hEqL hLlo (le_add_of_nonneg_right hhL.le) hLin
  obtain ⟨FR, hFR, hFRc, hFRg, hFRd⟩ := exists_morseCollarLogProfile_extension
    (p := b - hR) (q := b) hpqR hLamR hsR hrR hvR hEqR hRin (sub_le_self _ hhR.le) hRhi
  have hLrange (y : ℝ) (hy : y ∈ Icc a (a + hL)) :
      y ∈ (fun t => sL * rL t) '' Ioo pL qL := by
    rw [morseCollar_scaledRadius_image_Ioo hpqL hsL hrL hvL]
    exact ⟨hLlo.trans_le hy.1, hy.2.trans_lt hLin⟩
  have hRrange (y : ℝ) (hy : y ∈ Icc (b - hR) b) :
      y ∈ (fun t => sR * rR t) '' Ioo pR qR := by
    rw [morseCollar_scaledRadius_image_Ioo hpqR hsR hrR hvR]
    exact ⟨hRin.trans_le hy.1, hy.2.trans_lt hRhi⟩
  have hleft (y : ℝ) (hy : y ∈ Icc a (a + hL)) : m ≤ deriv FL y := by
    obtain ⟨t, ht, rfl⟩ := hLrange y hy
    rw [(hFLd t ht hy).deriv]
    exact hFloorL t ht hy
  have hright (y : ℝ) (hy : y ∈ Icc (b - hR) b) : m ≤ deriv FR y := by
    obtain ⟨t, ht, rfl⟩ := hRrange y hy
    rw [(hFRd t ht hy).deriv]
    exact hFloorR t ht hy
  have hsep' : a + hL < b - hR := hsep
  have hab : a ≤ b := by linarith only [hhL, hhR, hsep']
  have hbudget' : MorseJoinBudget a b hL hR m FL FR :=
    (morseJoinBudget_congr_of_germs hab hhL hhR hFLg hFRg).mpr hbudget
  let F := morseJoinLog a b hL hR FL FR
  let w := morseJoinProfile a b hL hR FL FR
  have hFs : ContDiff ℝ ∞ F := contDiff_morseJoinLog hFL hFR
  obtain ⟨hFa, hFb⟩ := morseJoinLog_endpoint_germs hhL hhR hsep' hFL hFR
  have hFa' : F =ᶠ[𝓝 a] fL := hFa.trans (hFLg a ⟨le_rfl, le_add_of_nonneg_right hhL.le⟩)
  have hFb' : F =ᶠ[𝓝 b] fR := hFb.trans (hFRg b ⟨sub_le_self _ hhR.le, le_rfl⟩)
  have haInside : a ∈ Ioo (sL * rL pL) (sL * rL qL) :=
    ⟨hLlo, (le_add_of_nonneg_right hhL.le).trans_lt hLin⟩
  have hbInside : b ∈ Ioo (sR * rR pR) (sR * rR qR) :=
    ⟨hRin.trans_le (sub_le_self _ hhR.le), hRhi⟩
  have hWa : w =ᶠ[𝓝 a] fun y => lamL * sL * deriv rL (morseCollarCoordinate rL sL pL qL y) := by
    change (fun y => exp (F y)) =ᶠ[𝓝 a] _
    apply (hFa'.fun_comp exp).trans
    filter_upwards [isOpen_Ioo.mem_nhds haInside] with y hy
    exact exp_morseCollarLogProfile_eqOn hpqL hLamL hsL hrL hvL hy
  have hWb : w =ᶠ[𝓝 b] fun y => lamR * sR * deriv rR (morseCollarCoordinate rR sR pR qR y) := by
    change (fun y => exp (F y)) =ᶠ[𝓝 b] _
    apply (hFb'.fun_comp exp).trans
    filter_upwards [isOpen_Ioo.mem_nhds hbInside] with y hy
    exact exp_morseCollarLogProfile_eqOn hpqR hLamR hsR hrR hvR hy
  obtain ⟨hws, hwpos, hwd, hmono, hstrict⟩ :=
    morseJoinProfile_positive_mono hhL hhR hsep' hFL hFR hm hleft hright hbudget'
  have hFd := morseJoinLog_deriv_ge hhL hhR hsep' hFL hFR hleft hright hbudget'
  have hmiddle (y : ℝ) (hy : y ∈ Icc (a + hL) (b - hR)) :
      deriv F y = morseJoinConstant a b hL hR FL FR :=
    morseJoinLog_deriv_middle hhL hhR hFL hFR hy
  exact ⟨FL, FR, hFL, hFR, hFLc, hFRc, hFLg, hFRg, hbudget', hFs, hws, hFa', hFb',
    hWa, hWb, fun y hy => ⟨hFd y hy, hwd y hy⟩,
    hmiddle, hwpos, hmono, hstrict⟩

end ContinuousFlexibility.Radial
