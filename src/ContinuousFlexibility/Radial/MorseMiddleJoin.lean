import ContinuousFlexibility.Radial.MorseJoinActualGerms
import ContinuousFlexibility.Radial.MorsePositiveJoin

/-!
# A finite positive bridge between the two Morse tails

For the middle splice in §5, positivity of the two endpoint slopes and a
positive difference of logarithmic heights suffice. The two contributions
to the interpolation budget are bounded by the actual widths of their
cutoff supports. This permits an arbitrarily short pair of endpoint collars.
-/

noncomputable section
namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Only the interval of width `h` contributes to the left cutoff integral. -/
theorem morseMiddleJoin_left_integral_le {a b h K : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : 0 < h) (hab : a + h ≤ b) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ Icc a (a + h), deriv f x ≤ K) :
    (∫ x in a..b, morseJoinLeftSlope a h f x) ≤ K * h := by
  let g := morseJoinLeftSlope a h f
  have hg : Continuous g :=
    (contDiff_morseJoinLeftWeight a h).continuous.mul
      (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hzero : (∫ x in a + h..b, g x) = 0 := by
    calc
      _ = ∫ _ in a + h..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        simp only [g, morseJoinLeftSlope, morseJoinLeftWeight_zero hh hx.1, zero_mul]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable a (a + h)) (hg.intervalIntegrable (a + h) b)
  rw [hzero, add_zero] at hsplit
  calc
    (∫ x in a..b, g x) = ∫ x in a..a + h, g x := hsplit.symm
    _ ≤ ∫ _ in a..a + h, K := by
      apply intervalIntegral.integral_mono_on (le_add_of_nonneg_right hh.le)
        (hg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      intro x hx
      have hw : 0 ≤ morseJoinLeftWeight a h x := smoothTransition.nonneg _
      have hw' : morseJoinLeftWeight a h x ≤ 1 := smoothTransition.le_one _
      calc
        g x ≤ morseJoinLeftWeight a h x * K :=
          mul_le_mul_of_nonneg_left (hbound x hx) hw
        _ ≤ K := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw' hK
    _ = K * h := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- Only the interval of width `h` contributes to the right cutoff integral. -/
theorem morseMiddleJoin_right_integral_le {a b h K : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : 0 < h) (hab : a ≤ b - h) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ Icc (b - h) b, deriv f x ≤ K) :
    (∫ x in a..b, morseJoinRightSlope b h f x) ≤ K * h := by
  let g := morseJoinRightSlope b h f
  have hg : Continuous g :=
    (contDiff_morseJoinRightWeight b h).continuous.mul
      (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hzero : (∫ x in a..b - h, g x) = 0 := by
    calc
      _ = ∫ _ in a..b - h, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        simp only [g, morseJoinRightSlope, morseJoinRightWeight_zero hh hx.2, zero_mul]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable a (b - h)) (hg.intervalIntegrable (b - h) b)
  rw [hzero, zero_add] at hsplit
  calc
    (∫ x in a..b, g x) = ∫ x in b - h..b, g x := hsplit.symm
    _ ≤ ∫ _ in b - h..b, K := by
      apply intervalIntegral.integral_mono_on (sub_le_self _ hh.le)
        (hg.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      intro x hx
      have hw : 0 ≤ morseJoinRightWeight b h x := smoothTransition.nonneg _
      have hw' : morseJoinRightWeight b h x ≤ 1 := smoothTransition.le_one _
      calc
        g x ≤ morseJoinRightWeight b h x * K :=
          mul_le_mul_of_nonneg_left (hbound x hx) hw
        _ ≤ K := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw' hK
    _ = K * h := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem exists_morseMiddleJoin_deriv_bounds {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiff ℝ ∞ f) (hd : 0 < deriv f x) :
    ∃ d > 0, ∀ y, |y - x| < d →
      deriv f x / 2 ≤ deriv f y ∧ deriv f y ≤ 2 * deriv f x := by
  have hc : ContinuousAt (deriv f) x :=
    (contDiff_infty_iff_deriv.mp hf).2.continuous.continuousAt
  obtain ⟨d, hdpos, h⟩ := Metric.continuousAt_iff.mp hc (deriv f x / 2) (by positivity)
  refine ⟨d, hdpos, fun y hy => ?_⟩
  have hdy : |deriv f y - deriv f x| < deriv f x / 2 :=
    by simpa only [Real.dist_eq] using h (x := y) (by simpa only [Real.dist_eq] using hy)
  obtain ⟨hl, hu⟩ := abs_lt.mp hdy
  exact ⟨by linarith only [hl], by linarith only [hu, hd]⟩

/-- A positive log gap pays for both cutoffs and a positive slope floor. -/
theorem exists_morseMiddleJoin_cutoff_budget {a b eta : ℝ} {fL fR : ℝ → ℝ}
    (hab : a < b) (heta : 0 < eta) (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hdL : 0 < deriv fL a) (hdR : 0 < deriv fR b) (hgap : fL a < fR b) :
    ∃ h m : ℝ, 0 < h ∧ h < eta ∧ a + h < b - h ∧ 0 < m ∧
      (∀ x ∈ Icc a (a + h), m ≤ deriv fL x) ∧
      (∀ x ∈ Icc (b - h) b, m ≤ deriv fR x) ∧
      MorseJoinBudget a b h h m fL fR := by
  obtain ⟨dL, hdLpos, hL⟩ := exists_morseMiddleJoin_deriv_bounds hfL hdL
  obtain ⟨dR, hdRpos, hR⟩ := exists_morseMiddleJoin_deriv_bounds hfR hdR
  let G := fR b - fL a
  let D := b - a
  let KL := 2 * deriv fL a
  let KR := 2 * deriv fR b
  have hG : 0 < G := sub_pos.mpr hgap
  have hD : 0 < D := sub_pos.mpr hab
  have hKL : 0 < KL := mul_pos (by norm_num) hdL
  have hKR : 0 < KR := mul_pos (by norm_num) hdR
  have hden : 0 < 4 * (KL + KR) := by positivity
  have hDden : 0 < 4 * D := by positivity
  let h := min (min (dL / 2) (dR / 2)) (min (eta / 2) (min (D / 4) (G / (4 * (KL + KR)))))
  let m := min (min (deriv fL a / 2) (deriv fR b / 2)) (G / (4 * D))
  have hh : 0 < h := by
    dsimp only [h]
    exact lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (lt_min (by positivity) (div_pos hG hden)))
  have hm : 0 < m :=
    lt_min (lt_min (by positivity) (by positivity)) (div_pos hG hDden)
  have hleft : h ≤ min (dL / 2) (dR / 2) := min_le_left _ _
  have hright : h ≤ min (eta / 2) (min (D / 4) (G / (4 * (KL + KR)))) := min_le_right _ _
  have htail : h ≤ min (D / 4) (G / (4 * (KL + KR))) :=
    hright.trans (min_le_right _ _)
  have hEta : h < eta := by
    have he := hright.trans (min_le_left _ _)
    linarith only [he, heta]
  have hsep : a + h < b - h := by
    have hd := htail.trans (min_le_left _ _)
    dsimp only [D] at hd
    linarith only [hd, hab]
  have hleftBounds (x : ℝ) (hx : x ∈ Icc a (a + h)) :
      m ≤ deriv fL x ∧ deriv fL x ≤ KL := by
    have hhL := hleft.trans (min_le_left _ _)
    have hnear : |x - a| < dL := by
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith only [hx.2, hhL, hdLpos]
    obtain ⟨hl, hu⟩ := hL x hnear
    have hmL : m ≤ deriv fL a / 2 := (min_le_left _ _).trans (min_le_left _ _)
    exact ⟨hmL.trans hl, hu⟩
  have hrightBounds (x : ℝ) (hx : x ∈ Icc (b - h) b) :
      m ≤ deriv fR x ∧ deriv fR x ≤ KR := by
    have hhR := hleft.trans (min_le_right _ _)
    have hnear : |x - b| < dR := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
      linarith only [hx.1, hhR, hdRpos]
    obtain ⟨hl, hu⟩ := hR x hnear
    have hmR : m ≤ deriv fR b / 2 := (min_le_left _ _).trans (min_le_right _ _)
    exact ⟨hmR.trans hl, hu⟩
  have hIL := morseMiddleJoin_left_integral_le hfL hh
    (hsep.le.trans (sub_le_self b hh.le)) hKL.le (fun x hx => (hleftBounds x hx).2)
  have hIR := morseMiddleJoin_right_integral_le hfR hh
    ((le_add_of_nonneg_right hh.le).trans hsep.le) hKR.le (fun x hx => (hrightBounds x hx).2)
  have hSlopeCost : KL * h + KR * h ≤ G / 4 := by
    have hi : h ≤ G / (4 * (KL + KR)) := htail.trans (min_le_right _ _)
    have hc := (le_div_iff₀ hden).mp hi
    nlinarith only [hc]
  have hFloorCost : m * morseJoinDenominator a b h h ≤ G / 4 := by
    calc
      _ ≤ m * D :=
        mul_le_mul_of_nonneg_left (morseJoinDenominator_bounds hh hh hsep.le).2 hm.le
      _ ≤ _ := by
        have hi : m ≤ G / (4 * D) := min_le_right _ _
        have hc := (le_div_iff₀ hDden).mp hi
        nlinarith only [hc]
  refine ⟨h, m, hh, hEta, hsep, hm, fun x hx => (hleftBounds x hx).1,
    fun x hx => (hrightBounds x hx).1, ?_⟩
  unfold MorseJoinBudget
  change _ ≤ G
  linarith only [hIL, hIR, hSlopeCost, hFloorCost, hG]

/-- The positive middle bridge for two globally extended log profiles. -/
theorem exists_morseMiddleJoin_of_log_profiles {a b eta : ℝ} {fL fR : ℝ → ℝ}
    (hab : a < b) (heta : 0 < eta) (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hdL : 0 < deriv fL a) (hdR : 0 < deriv fR b) (hgap : fL a < fR b) :
    ∃ h m : ℝ, 0 < h ∧ h < eta ∧ a + h < b - h ∧ 0 < m ∧
      MorseJoinBudget a b h h m fL fR ∧
      let w := morseJoinProfile a b h h fL fR
      ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
        (w =ᶠ[𝓝 a] fun x => exp (fL x)) ∧ (w =ᶠ[𝓝 b] fun x => exp (fR x)) ∧
        (∀ x ∈ Icc a b, m * w x ≤ deriv w x ∧ 0 < deriv w x) ∧
        StrictMonoOn w (Icc a b) := by
  obtain ⟨h, m, hh, hEta, hsep, hm, hL, hR, hbudget⟩ :=
    exists_morseMiddleJoin_cutoff_budget hab heta hfL hfR hdL hdR hgap
  obtain ⟨hws, hwp, hwd, _, hmono⟩ :=
    morseJoinProfile_positive_mono hh hh hsep hfL hfR hm.le hL hR hbudget
  obtain ⟨hwa, hwb⟩ := morseJoinProfile_endpoint_germs hh hh hsep hfL hfR
  exact ⟨h, m, hh, hEta, hsep, hm, hbudget, hws, hwp, hwa, hwb,
    fun x hx => ⟨hwd x hx, (mul_pos hm (hwp x)).trans_le (hwd x hx)⟩, hmono hm⟩

/-- The middle bridge preserves the genuine local logarithmic germs at
both endpoints and uses extensions agreeing on the entire cutoff collars. -/
theorem exists_morseMiddleJoin_of_log_germs {a b eta uL vL uR vR : ℝ} {fL fR : ℝ → ℝ}
    (hab : a < b) (heta : 0 < eta) (ha : a ∈ Ioo uL vL) (hb : b ∈ Ioo uR vR)
    (hfL : ContDiffOn ℝ ∞ fL (Ioo uL vL)) (hfR : ContDiffOn ℝ ∞ fR (Ioo uR vR))
    (hdL : 0 < deriv fL a) (hdR : 0 < deriv fR b) (hgap : fL a < fR b) :
    ∃ (h m : ℝ) (leftExt rightExt : ℝ → ℝ), 0 < h ∧ h < eta ∧
      a + h < b - h ∧ 0 < m ∧ ContDiff ℝ ∞ leftExt ∧ ContDiff ℝ ∞ rightExt ∧
      HasCompactSupport leftExt ∧ HasCompactSupport rightExt ∧
      (∀ x ∈ Icc a (a + h), leftExt =ᶠ[𝓝 x] fL) ∧
      (∀ x ∈ Icc (b - h) b, rightExt =ᶠ[𝓝 x] fR) ∧
      MorseJoinBudget a b h h m leftExt rightExt ∧
      let w := morseJoinProfile a b h h leftExt rightExt
      ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
        (w =ᶠ[𝓝 a] fun x => exp (fL x)) ∧ (w =ᶠ[𝓝 b] fun x => exp (fR x)) ∧
        (∀ x ∈ Icc a b, m * w x ≤ deriv w x ∧ 0 < deriv w x) ∧
        StrictMonoOn w (Icc a b) := by
  let e := min eta (min ((vL - a) / 2) ((b - uR) / 2))
  have he : 0 < e := lt_min heta (lt_min
    (div_pos (sub_pos.mpr ha.2) (by norm_num)) (div_pos (sub_pos.mpr hb.1) (by norm_num)))
  have heEta : e ≤ eta := min_le_left _ _
  have he' : e ≤ min ((vL - a) / 2) ((b - uR) / 2) := min_le_right _ _
  have heL : a + e < vL := by
    have h := he'.trans (min_le_left _ _)
    linarith only [h, ha.2]
  have heR : uR < b - e := by
    have h := he'.trans (min_le_right _ _)
    linarith only [h, hb.1]
  have hae : a ≤ a + e := le_add_of_nonneg_right he.le
  have hbe : b - e ≤ b := sub_le_self _ he.le
  obtain ⟨leftExt, hLs, hLc, hLg⟩ := exists_contDiff_joinGerm_extension ha.1 hae heL hfL
  obtain ⟨rightExt, hRs, hRc, hRg⟩ := exists_contDiff_joinGerm_extension heR hbe hb.2 hfR
  have hLa := hLg a ⟨le_rfl, hae⟩
  have hRb := hRg b ⟨hbe, le_rfl⟩
  obtain ⟨h, m, hh, hhe, hsep, hm, hbudget, hws, hwp, hwa, hwb, hwd, hmono⟩ :=
    exists_morseMiddleJoin_of_log_profiles hab he hLs hRs
      (by simpa only [hLa.deriv_eq] using hdL) (by simpa only [hRb.deriv_eq] using hdR)
      (by simpa only [hLa.eq_of_nhds, hRb.eq_of_nhds] using hgap)
  have heL' : a + h ≤ a + e := by linarith only [hhe]
  have heR' : b - e ≤ b - h := by linarith only [hhe]
  exact ⟨h, m, leftExt, rightExt, hh, hhe.trans_le heEta, hsep, hm, hLs, hRs, hLc, hRc,
    fun x hx => hLg x ⟨hx.1, hx.2.trans heL'⟩, fun x hx => hRg x ⟨heR'.trans hx.1, hx.2⟩,
    hbudget, hws, hwp, hwa.trans (hLa.fun_comp exp), hwb.trans (hRb.fun_comp exp), hwd, hmono⟩

/-- The incoming short cap has higher physical height than the outgoing
long cap at the same index. The common amplitude cancels. -/
theorem morseMiddleJoin_same_amplitude_gap {A lam sL sR rL rR vL vR : ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (hlam : 0 < lam) (hsL : 0 < sL) (hsR : 0 < sR)
    (hrL : 1 / 2 ≤ rL) (hrR : rR ≤ 2) (hab : sL * rL < sR * rR)
    (hvL : vL ≤ (3 / 100) * A ^ 5) (hvR : A / 4 ≤ vR) :
    lam * sL * vL < lam * sR * vR := by
  have hsLR : sL ≤ 4 * sR := by
    have hL := mul_le_mul_of_nonneg_left hrL hsL.le
    have hR := mul_le_mul_of_nonneg_left hrR hsR.le
    linarith only [hL, hab, hR]
  have hpow : A ^ 5 ≤ A := by
    calc
      A ^ 5 = A * A ^ 4 := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hA.le hA1) hA.le
      _ = A := mul_one A
  have hvL' : vL ≤ (3 / 100) * A :=
    hvL.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hgap : sL * vL < sR * vR := by
    calc
      sL * vL ≤ sL * ((3 / 100) * A) := mul_le_mul_of_nonneg_left hvL' hsL.le
      _ ≤ (4 * sR) * ((3 / 100) * A) := mul_le_mul_of_nonneg_right hsLR (by positivity)
      _ < sR * (A / 4) := by nlinarith only [mul_pos hsR hA]
      _ ≤ sR * vR := mul_le_mul_of_nonneg_left hvR hsR.le
  calc
    lam * sL * vL = lam * (sL * vL) := mul_assoc _ _ _
    _ < lam * (sR * vR) := mul_lt_mul_of_pos_left hgap hlam
    _ = lam * sR * vR := (mul_assoc _ _ _).symm

/-- A finite middle bridge for actual retained cap germs, with the same
Morse parameters and height amplitude at the two endpoints. The radius
ordering and the cap slope estimates imply the required log gap. -/
theorem exists_morseMiddleJoin_of_model_germs {A B lam sL sR pL qL pR qR eta : ℝ}
    {rL rR : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hA1 : A ≤ 1)
    (hlam : 0 < lam) (hsL : 0 < sL) (hsR : 0 < sR) (heta : 0 < eta)
    (hrL : ContDiff ℝ ∞ rL) (hrR : ContDiff ℝ ∞ rR)
    (hvL : ∀ x ∈ Ioo pL qL, 0 < deriv rL x) (hvR : ∀ x ∈ Ioo pR qR, 0 < deriv rR x)
    (hEqL : ∀ x ∈ Ioo pL qL, deriv (deriv rL) x = -morseRho A B x * rL x)
    (hEqR : ∀ x ∈ Ioo pR qR, deriv (deriv rR) x = -morseRho A B x * rR x)
    (hxL : morseRightCapEnd A B (1 / 100) ∈ Ioo pL qL) (hxR : morseCellLeftCut ∈ Ioo pR qR)
    (hrLe : 1 / 2 ≤ rL (morseRightCapEnd A B (1 / 100)))
    (hrRe : rR morseCellLeftCut ≤ 2)
    (hvLe : deriv rL (morseRightCapEnd A B (1 / 100)) ≤ (3 / 100) * A ^ 5)
    (hvRe : A / 4 ≤ deriv rR morseCellLeftCut)
    (hab : sL * rL (morseRightCapEnd A B (1 / 100)) < sR * rR morseCellLeftCut) :
    let a := sL * rL (morseRightCapEnd A B (1 / 100))
    let b := sR * rR morseCellLeftCut
    let fL := morseCollarLogProfile rL lam sL pL qL
    let fR := morseCollarLogProfile rR lam sR pR qR
    ∃ (h m : ℝ) (leftExt rightExt : ℝ → ℝ), 0 < h ∧ h < eta ∧
      a + h < b - h ∧ 0 < m ∧ ContDiff ℝ ∞ leftExt ∧ ContDiff ℝ ∞ rightExt ∧
      (∀ x ∈ Icc a (a + h), leftExt =ᶠ[𝓝 x] fL) ∧
      (∀ x ∈ Icc (b - h) b, rightExt =ᶠ[𝓝 x] fR) ∧
      MorseJoinBudget a b h h m leftExt rightExt ∧
      let w := morseJoinProfile a b h h leftExt rightExt
      ContDiff ℝ ∞ w ∧ (∀ x, 0 < w x) ∧
        (w =ᶠ[𝓝 a] fun y => lam * sL * deriv rL (morseCollarCoordinate rL sL pL qL y)) ∧
        (w =ᶠ[𝓝 b] fun y => lam * sR * deriv rR (morseCollarCoordinate rR sR pR qR y)) ∧
        (∀ x ∈ Icc a b, m * w x ≤ deriv w x ∧ 0 < deriv w x) ∧
        StrictMonoOn w (Icc a b) := by
  let xL := morseRightCapEnd A B (1 / 100)
  let xR := morseCellLeftCut
  let a := sL * rL xL
  let b := sR * rR xR
  let fL := morseCollarLogProfile rL lam sL pL qL
  let fR := morseCollarLogProfile rR lam sR pR qR
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hLpos : 0 < rL xL := lt_of_lt_of_le (by norm_num) hrLe
  have hRpos : 0 < rR xR := pos_of_mul_pos_right ((mul_pos hsL hLpos).trans hab) hsR.le
  have hρL : morseRho A B xL < 0 :=
    morseRho_neg_after_right_turn hB hAB
      (lt_add_of_pos_right _ (morseRightCapLength_pos hA (by norm_num)))
  have hρR : morseRho A B xR < 0 := by
    have h0 : xR < 0 := neg_lt_zero.mpr (log_pos (by norm_num : (1 : ℝ) < 3 / 2))
    have hTL : 0 < morseLeftRootT A B := (by norm_num : (0 : ℝ) < 1 / 2).trans
      (morseRootT_bounds hB hAB).2.2.1
    have hTurn : 0 < morseLeftTurn A B :=
      neg_pos.mpr (log_neg hTL (morseRootT_bounds hB hAB).2.2.2)
    exact morseRho_neg_before_left_turn hB hAB (h0.trans hTurn)
  have hpqL := hxL.1.le.trans hxL.2.le
  have hpqR := hxR.1.le.trans hxR.2.le
  have ha : a ∈ Ioo (sL * rL pL) (sL * rL qL) := by
    rw [← morseCollar_scaledRadius_image_Ioo hpqL hsL hrL hvL]
    exact ⟨xL, hxL, rfl⟩
  have hb : b ∈ Ioo (sR * rR pR) (sR * rR qR) := by
    rw [← morseCollar_scaledRadius_image_Ioo hpqR hsR hrR hvR]
    exact ⟨xR, hxR, rfl⟩
  have hdL : 0 < deriv fL a := by
    rw [(morseCollarLogProfile_jet hlam hsL hrL hvL hxL (hEqL xL hxL)).2.2.deriv]
    exact div_pos (mul_pos (neg_pos.mpr hρL) hLpos) (mul_pos hsL (pow_pos (hvL xL hxL) 2))
  have hdR : 0 < deriv fR b := by
    rw [(morseCollarLogProfile_jet hlam hsR hrR hvR hxR (hEqR xR hxR)).2.2.deriv]
    exact div_pos (mul_pos (neg_pos.mpr hρR) hRpos) (mul_pos hsR (pow_pos (hvR xR hxR) 2))
  have hgap : fL a < fR b := by
    dsimp only [fL, fR, a, b]
    rw [morseCollarLogProfile_at_model hsL hrL hvL hxL,
      morseCollarLogProfile_at_model hsR hrR hvR hxR]
    exact log_lt_log (mul_pos (mul_pos hlam hsL) (hvL xL hxL))
      (morseMiddleJoin_same_amplitude_gap hA hA1 hlam hsL hsR hrLe hrRe hab hvLe hvRe)
  obtain ⟨h, m, leftExt, rightExt, hh, hEta, hsep, hm, hLs, hRs, _, _, hLg, hRg,
    hbudget, hws, hwp, hwa, hwb, hwd, hmono⟩ :=
    exists_morseMiddleJoin_of_log_germs hab heta ha hb
      (contDiffOn_morseCollarLogProfile hpqL hlam hsL hrL hvL hEqL)
      (contDiffOn_morseCollarLogProfile hpqR hlam hsR hrR hvR hEqR) hdL hdR hgap
  have hga : (fun y => exp (fL y)) =ᶠ[𝓝 a]
      fun y => lam * sL * deriv rL (morseCollarCoordinate rL sL pL qL y) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with y hy
    exact exp_morseCollarLogProfile_eqOn hpqL hlam hsL hrL hvL hy
  have hgb : (fun y => exp (fR y)) =ᶠ[𝓝 b]
      fun y => lam * sR * deriv rR (morseCollarCoordinate rR sR pR qR y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hb] with y hy
    exact exp_morseCollarLogProfile_eqOn hpqR hlam hsR hrR hvR hy
  exact ⟨h, m, leftExt, rightExt, hh, hEta, hsep, hm, hLs, hRs, hLg, hRg, hbudget,
    hws, hwp, hwa.trans hga, hwb.trans hgb, hwd, hmono⟩

end ContinuousFlexibility.Radial
