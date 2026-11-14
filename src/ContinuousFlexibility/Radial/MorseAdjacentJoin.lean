module

public import ContinuousFlexibility.Radial.MorseJoinActualGerms
public import ContinuousFlexibility.Radial.MorseJoinHeightContrast
public import ContinuousFlexibility.Radial.MorseChainRadiusPlacement

/-!
# An actual join between two adjacent Morse cells

The two physical support collars have length one quarter of the connector.
The model ODE controls their logarithmic derivatives, and the actual height
contrast supplies the integral budget for the cutoff construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Orient the two radius placement equations in the direction of increasing radius. -/
theorem morseAdjacentJoin_placement_width {A l u : ℕ → ℝ} {S : Bool → ℕ → ℝ}
    {c : ℝ} {k : ℕ}
    (hR : S true (k + 1) * l (k + 1) - S true k * u k =
      S true k * u k * morseChainJoinFraction A c k)
    (hL : S false k * l k - S false (k + 1) * u (k + 1) =
      S false (k + 1) * u (k + 1) * morseChainJoinFraction A c k) (side : Bool) :
    let n := if side then k else k + 1
    let m := if side then k + 1 else k
    S side m * l m - S side n * u n = c * (S side n * u n) * (min (A n) (A m)) ^ 12 := by
  cases side
  · change S false k * l k - S false (k + 1) * u (k + 1) =
      c * (S false (k + 1) * u (k + 1)) * (min (A (k + 1)) (A k)) ^ 12
    rw [hL, morseChainJoinFraction, min_comm (A (k + 1)) (A k)]
    ring
  · change S true (k + 1) * l (k + 1) - S true k * u k =
      c * (S true k * u k) * (min (A k) (A (k + 1))) ^ 12
    rw [hR, morseChainJoinFraction]
    ring

private theorem morseAdjacentJoin_small_A (T : Statements.MorseChainData) (n : ℕ)
    (hn : 10 ≤ n) (hd : T.d n = morseChainInteger n) :
    Statements.morseChainA T n ≤ 25 / (2 * (9 : ℝ) ^ 9) := by
  have hlog : log (9 / (25 / (2 * (9 : ℝ) ^ 9))) ≤ 80 := calc
    _ ≤ log ((9 : ℝ) ^ 10) := log_le_log (by positivity) (by norm_num)
    _ = 10 * log (9 : ℝ) := by rw [log_pow]; norm_num
    _ ≤ _ := by
      have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
      linarith only [h]
  have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hn' 2
  exact morseChainA_le_of_sq_ge_log T n hd (by positivity) (by linarith only [hlog, hs])

private theorem morseAdjacentJoin_scaled_increment {r : ℝ → ℝ} {s x y v : ℝ}
    (hr : ContDiff ℝ ∞ r) (hs : 0 ≤ s) (hxy : x ≤ y)
    (hv : ∀ t ∈ Icc x y, v ≤ deriv r t) :
    s * (y - x) * v ≤ s * r y - s * r x := by
  have hi : IntervalIntegrable (deriv r) volume x y :=
    (contDiff_infty_iff_deriv.mp hr).2.continuous.intervalIntegrable x y
  have hFTC : (∫ t in x..y, deriv r t) = r y - r x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hr.differentiable (by simp) t).hasDerivAt) hi
  have h := intervalIntegral.integral_mono_on hxy
    ((continuous_const : Continuous (fun _ : ℝ => v)).intervalIntegrable x y) hi hv
  rw [intervalIntegral.integral_const, smul_eq_mul, hFTC] at h
  calc
    _ = s * ((y - x) * v) := by ring
    _ ≤ s * (r y - r x) := mul_le_mul_of_nonneg_left h hs
    _ = _ := mul_sub _ _ _

private theorem morseAdjacentJoin_quarter_small {s A h : ℝ}
    (hs : 0 < s) (hA : 0 < A) (hA₀ : A ≤ 1 / 1000)
    (hh : h ≤ (s / 2) * A ^ 12) :
    h < s * morseJoinCollarWidth * (A ^ 5 / 200) ∧
      h < s * morseJoinCollarWidth * (A / 5) := by
  have h7 : A ^ 7 ≤ (1 / 1000 : ℝ) ^ 7 := pow_le_pow_left₀ hA.le hA₀ 7
  have h11 : A ^ 11 ≤ (1 / 1000 : ℝ) ^ 11 := pow_le_pow_left₀ hA.le hA₀ 11
  have h7' : A ^ 7 / 2 < morseJoinCollarWidth / 200 := by
    unfold morseJoinCollarWidth
    linarith only [h7]
  have h11' : A ^ 11 / 2 < morseJoinCollarWidth / 5 := by
    unfold morseJoinCollarWidth
    linarith only [h11]
  constructor
  · calc
      h ≤ (s / 2) * A ^ 12 := hh
      _ = (s * A ^ 5) * (A ^ 7 / 2) := by ring
      _ < (s * A ^ 5) * (morseJoinCollarWidth / 200) :=
        mul_lt_mul_of_pos_left h7' (mul_pos hs (pow_pos hA 5))
      _ = _ := by ring
  · calc
      h ≤ (s / 2) * A ^ 12 := hh
      _ = (s * A) * (A ^ 11 / 2) := by ring
      _ < (s * A) * (morseJoinCollarWidth / 5) := mul_lt_mul_of_pos_left h11' (mul_pos hs hA)
      _ = _ := by ring

private theorem morseAdjacentJoin_quarter_le {a c s A U : ℝ}
    (ha : 0 ≤ a) (hc₁ : c ≤ 1) (hs : 0 ≤ s)
    (has : a ≤ 2 * s) (hU : 0 ≤ U) (hUA : U ≤ A) :
    c * a * U ^ 12 / 4 ≤ (s / 2) * A ^ 12 := by
  have hca : c * a ≤ 2 * s :=
    (mul_le_mul_of_nonneg_right hc₁ ha).trans (by simpa only [one_mul] using has)
  calc
    _ ≤ ((2 * s) * A ^ 12) / 4 := div_le_div_of_nonneg_right
      (mul_le_mul hca (pow_le_pow_left₀ hU hUA 12) (pow_nonneg hU 12) (by positivity)) (by norm_num)
    _ = _ := by ring

private theorem morseAdjacentJoin_floor {a s A : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hA : 0 < A) (hsa : s / 4 ≤ a) (hA₀ : A ≤ 25 / (2 * (9 : ℝ) ^ 9)) :
    2 / a ≤ (100 / (9 : ℝ) ^ 9) / (s * A) := by
  apply (div_le_div_iff₀ ha (mul_pos hs hA)).mpr
  calc
    2 * (s * A) = s * (2 * A) := by ring
    _ ≤ s * (25 / (9 : ℝ) ^ 9) := mul_le_mul_of_nonneg_left (by linarith only [hA₀]) hs.le
    _ = (100 / (9 : ℝ) ^ 9) * (s / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsa (by positivity)

private theorem morseAdjacentJoin_budget_lt_one {a c sL sR AL AR U : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hc₁ : c ≤ 1) (hsL : 0 < sL) (hsR : 0 < sR)
    (hAL : 0 < AL) (hAR : 0 < AR) (haL : a ≤ 2 * sL) (haR : a ≤ 2 * sR)
    (hU : 0 < U) (hUL : U ≤ AL) (hUR : U ≤ AR) (hU₀ : U ≤ 1 / 1000) :
    let ell := c * a * U ^ 12
    (100000 / (sL * AL) + 100000 / (sR * AR) + 2 / a) * ell ≤
      c * (400000 * U ^ 11 + 2 * U ^ 12) ∧
    c * (400000 * U ^ 11 + 2 * U ^ 12) < 1 := by
  let ell := c * a * U ^ 12
  have hpart (s A : ℝ) (hs : 0 < s) (hA : 0 < A) (has : a ≤ 2 * s) (hUA : U ≤ A) :
      (100000 / (s * A)) * ell ≤ c * (200000 * U ^ 11) := by
    have has' : a / s ≤ 2 := (div_le_iff₀ hs).mpr has
    have hrat : U ^ 12 / A ≤ U ^ 11 := by
      apply (div_le_iff₀ hA).mpr
      rw [show U ^ 12 = U ^ 11 * U by ring]
      exact mul_le_mul_of_nonneg_left hUA (pow_nonneg hU.le 11)
    calc
      _ = (c * 100000) * ((a / s) * (U ^ 12 / A)) := by
        dsimp only [ell]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (c * 100000) * (2 * U ^ 11) :=
        mul_le_mul_of_nonneg_left (mul_le_mul has' hrat (by positivity) (by norm_num)) (by positivity)
      _ = _ := by ring
  have hm : (2 / a) * ell = c * (2 * U ^ 12) := calc
    _ = (a * a⁻¹) * (c * (2 * U ^ 12)) := by dsimp only [ell]; rw [div_eq_mul_inv]; ring
    _ = _ := by rw [mul_inv_cancel₀ ha.ne', one_mul]
  have hsum : (100000 / (sL * AL) + 100000 / (sR * AR) + 2 / a) * ell ≤
      c * (400000 * U ^ 11 + 2 * U ^ 12) := calc
    _ = (100000 / (sL * AL)) * ell + (100000 / (sR * AR)) * ell + (2 / a) * ell := by ring
    _ ≤ c * (200000 * U ^ 11) + c * (200000 * U ^ 11) + c * (2 * U ^ 12) :=
      add_le_add (add_le_add (hpart sL AL hsL hAL haL hUL) (hpart sR AR hsR hAR haR hUR)) hm.le
    _ = _ := by ring
  refine ⟨hsum, ?_⟩
  have h11 := pow_le_pow_left₀ hU.le hU₀ 11
  have h12 := pow_le_pow_left₀ hU.le hU₀ 12
  calc
    _ ≤ 1 * (400000 * U ^ 11 + 2 * U ^ 12) := mul_le_mul_of_nonneg_right hc₁ (by positivity)
    _ ≤ 400000 * (1 / 1000 : ℝ) ^ 11 + 2 * (1 / 1000 : ℝ) ^ 12 := by linarith only [h11, h12]
    _ < _ := by norm_num

private theorem morseAdjacentJoin_scaled_mono {p q s : ℝ} {r : ℝ → ℝ}
    (hs : 0 < s) (hr : ContDiff ℝ ∞ r) (hv : ∀ x ∈ Ioo p q, 0 < deriv r x) :
    StrictMonoOn (fun x => s * r x) (Ioo p q) := by
  have hc : Continuous (fun x => s * r x) := continuous_const.mul hr.continuous
  apply strictMonoOn_of_deriv_pos (convex_Ioo p q) hc.continuousOn
  intro x hx
  have hD : HasDerivAt (fun x => s * r x) (s * deriv r x) x :=
    ((hr.differentiable (by simp) x).hasDerivAt).const_mul s
  rw [hD.deriv]
  exact mul_pos hs (hv x (interior_subset hx))

/-- Join the right endpoint of the departing model to the left endpoint of
its neighbor. The two outer collar bounds are those of the same ODE solutions
used on the retained cells. The placement equation can use either orientation
of `morseAdjacentJoin_placement_width`. -/
theorem exists_morseAdjacentJoin_with_model_germs (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ} (hn : 100 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    {c sL sR : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hsL : 0 < sL) (hsR : 0 < sR)
    {rL rR : ℝ → ℝ} (hrL : ContDiff ℝ ∞ rL) (hrR : ContDiff ℝ ∞ rR) :
    let AL := Statements.morseChainA T n
    let BL := Statements.morseChainB T n
    let AR := Statements.morseChainA T m
    let BR := Statements.morseChainB T m
    let p := morseCellLeftCut - morseJoinCollarWidth
    let eL := morseRightCapEnd AL BL (1 / 100)
    let qL := eL + morseJoinCollarWidth
    let qR := morseRightCapEnd AR BR (1 / 100) + morseJoinCollarWidth
    let a := sL * rL eL
    let b := sR * rR morseCellLeftCut
    let ell := c * a * (min AL AR) ^ 12
    let h := ell / 4
    (∀ x ∈ Ioo p qL, 0 < deriv rL x) →
    (∀ x ∈ Ioo p qR, 0 < deriv rR x) →
    (∀ x ∈ Ioo p qL, deriv (deriv rL) x = -morseRho AL BL x * rL x) →
    (∀ x ∈ Ioo p qR, deriv (deriv rR) x = -morseRho AR BR x * rR x) →
    (∀ x ∈ Icc eL qL,
      (1 / 2 : ℝ) ≤ rL x ∧ rL x ≤ 2 ∧ AL ^ 5 / 200 ≤ deriv rL x ∧
      deriv rL x ≤ AL ^ 5 / 25 ∧ BL / 2 ≤ -morseRho AL BL x ∧ -morseRho AL BL x ≤ BL) →
    (∀ x ∈ Icc p morseCellLeftCut,
      (1 / 2 : ℝ) ≤ rR x ∧ rR x ≤ 2 ∧ AR / 5 ≤ deriv rR x ∧ deriv rR x ≤ 8 * AR ∧
      (3 / 4 : ℝ) * AR ≤ -morseRho AR BR x ∧ -morseRho AR BR x ≤ 7 * AR) →
    ((1 / 100 : ℝ) * AL ^ 5 ≤ deriv rL eL ∧ deriv rL eL ≤ (3 / 100 : ℝ) * AL ^ 5) →
    (AR / 4 ≤ deriv rR morseCellLeftCut ∧ deriv rR morseCellLeftCut ≤ 7 * AR) →
    b - a = ell →
    ∃ FL FR : ℝ → ℝ, ContDiff ℝ ∞ FL ∧ ContDiff ℝ ∞ FR ∧
      (∀ y ∈ Icc a (a + h), FL =ᶠ[𝓝 y]
        morseCollarLogProfile rL (Statements.morseChainAmplitude T σ n) sL p qL) ∧
      (∀ y ∈ Icc (b - h) b, FR =ᶠ[𝓝 y]
        morseCollarLogProfile rR (Statements.morseChainAmplitude T σ m) sR p qR) ∧
      MorseJoinBudget a b h h (2 / a) FL FR ∧
      let w := morseJoinProfile a b h h FL FR
      ContDiff ℝ ∞ w ∧ (∀ y, 0 < w y) ∧
      (w =ᶠ[𝓝 a] fun y => Statements.morseChainAmplitude T σ n * sL *
        deriv rL (morseCollarCoordinate rL sL p qL y)) ∧
      (w =ᶠ[𝓝 b] fun y => Statements.morseChainAmplitude T σ m * sR *
        deriv rR (morseCollarCoordinate rR sR p qR y)) ∧
      (∀ y ∈ Icc a b, 2 / y ≤ deriv w y / w y) ∧ StrictMonoOn w (Icc a b) := by
  dsimp only
  let AL := Statements.morseChainA T n
  let BL := Statements.morseChainB T n
  let AR := Statements.morseChainA T m
  let BR := Statements.morseChainB T m
  let hM := morseJoinCollarWidth
  let p := morseCellLeftCut - hM
  let eL := morseRightCapEnd AL BL (1 / 100)
  let qL := eL + hM
  let qR := morseRightCapEnd AR BR (1 / 100) + hM
  let a := sL * rL eL
  let b := sR * rR morseCellLeftCut
  let U := min AL AR
  let ell := c * a * U ^ 12
  let h := ell / 4
  let floor := 2 / a
  let KL := 100000 / (sL * AL)
  let KR := 100000 / (sR * AR)
  let lamL := Statements.morseChainAmplitude T σ n
  let lamR := Statements.morseChainAmplitude T σ m
  let fL := morseCollarLogProfile rL lamL sL p qL
  let fR := morseCollarLogProfile rR lamR sR p qR
  intro hvL hvR hEqL hEqR hLc hRc hvEndL hvEndR hPlace
  have hwidth : b - a = ell := hPlace
  have hdn₂ : (2 : ℝ) ≤ T.d n := by rw [hdn]; exact_mod_cast morseChainInteger_ge_two n
  have hdm₂ : (2 : ℝ) ≤ T.d m := by rw [hdm]; exact_mod_cast morseChainInteger_ge_two m
  obtain ⟨hAB_L, hBL⟩ := morseChainParameters_pos T n hdn₂
  obtain ⟨hAB_R, hBR⟩ := morseChainParameters_pos T m hdm₂
  have hAL : 0 < AL := (mul_pos (by norm_num) hBL).trans hAB_L
  have hAR : 0 < AR := (mul_pos (by norm_num) hBR).trans hAB_R
  have hBAL := morseChainB_A_bounds T n ((by norm_num : (1 : ℝ) ≤ 2).trans hdn₂)
  have hBAR := morseChainB_A_bounds T m ((by norm_num : (1 : ℝ) ≤ 2).trans hdm₂)
  have hALs : AL ≤ 25 / (2 * (9 : ℝ) ^ 9) := morseAdjacentJoin_small_A T n (by omega) hdn
  have hARs : AR ≤ 25 / (2 * (9 : ℝ) ^ 9) :=
    morseAdjacentJoin_small_A T m (by rcases hadj with hstep | hstep <;> omega) hdm
  have hAL₀ : AL ≤ 1 / 1000 := hALs.trans (by norm_num)
  have hAR₀ : AR ≤ 1 / 1000 := hARs.trans (by norm_num)
  have hU : 0 < U := lt_min hAL hAR
  have hUL : U ≤ AL := min_le_left _ _
  have hUR : U ≤ AR := min_le_right _ _
  have hhM : 0 < hM := by norm_num [hM, morseJoinCollarWidth]
  have hpeL : p < eL :=
    (sub_lt_self _ hhM).trans_le ((morseCellLeftCut_lt_rightTurn hBL hAB_L).le.trans
      (le_add_of_nonneg_right (morseRightCapLength_pos hAL (by norm_num : (0 : ℝ) < 1 / 100)).le))
  have hceR : morseCellLeftCut < morseRightCapEnd AR BR (1 / 100) :=
    (morseCellLeftCut_lt_rightTurn hBR hAB_R).trans_le
      (le_add_of_nonneg_right (morseRightCapLength_pos hAR (by norm_num : (0 : ℝ) < 1 / 100)).le)
  have hxL : eL ∈ Ioo p qL := ⟨hpeL, lt_add_of_pos_right _ hhM⟩
  have hxR : morseCellLeftCut ∈ Ioo p qR :=
    ⟨sub_lt_self _ hhM, hceR.trans_le (le_add_of_nonneg_right hhM.le)⟩
  have hpqL := (hxL.1.trans hxL.2).le
  have hpqR := (hxR.1.trans hxR.2).le
  have hLe := hLc eL (left_mem_Icc.mpr hxL.2.le)
  have hRe := hRc morseCellLeftCut (right_mem_Icc.mpr hxR.1.le)
  have haL₀ : sL / 2 ≤ a := by
    calc
      _ = sL * (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLe.1 hsL.le
  have ha : 0 < a := (div_pos hsL (by norm_num : (0 : ℝ) < 2)).trans_le haL₀
  have haL : a ≤ 2 * sL :=
    (mul_le_mul_of_nonneg_left hLe.2.1 hsL.le).trans_eq (mul_comm _ _)
  have hbR₀ : sR / 2 ≤ b := by
    calc
      _ = sR * (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hRe.1 hsR.le
  have hbR : b ≤ 2 * sR :=
    (mul_le_mul_of_nonneg_left hRe.2.1 hsR.le).trans_eq (mul_comm _ _)
  have hell : 0 < ell := mul_pos (mul_pos hc ha) (pow_pos hU 12)
  have hab : a < b := by linarith only [hwidth, hell]
  have haR : a ≤ 2 * sR := hab.le.trans hbR
  let ε := c * U ^ 12
  have hε₀ : 0 ≤ ε := mul_nonneg hc.le (pow_nonneg hU.le _)
  have hε₁ : ε ≤ 1 := calc
    _ ≤ (1 : ℝ) * (1 : ℝ) ^ 12 := mul_le_mul hc₁
      (pow_le_pow_left₀ hU.le (hUL.trans (hAL₀.trans (by norm_num))) 12)
      (pow_nonneg hU.le 12) (by norm_num)
    _ = _ := by norm_num
  have hmatch : b = a * (1 + ε) := calc
    b = a + ell := by linarith only [hwidth]
    _ = _ := by dsimp only [ell, ε]; ring
  have hb2 : b ≤ 2 * a := calc
    _ = a * (1 + ε) := hmatch
    _ ≤ a * 2 := mul_le_mul_of_nonneg_left (by linarith only [hε₁]) ha.le
    _ = _ := mul_comm _ _
  have haR₀ : sR / 4 ≤ a := by linarith only [hbR₀, hb2]
  have hslog := morseJoin_scaleRatio_log_bound hsL hsR
    ⟨hLe.1, hLe.2.1⟩ ⟨hRe.1, hRe.2.1⟩ ⟨hε₀, hε₁⟩ hmatch
  have hh : 0 < h := div_pos hell (by norm_num)
  have hsep : a + h < b - h := by dsimp only [h]; linarith only [hwidth, hell]
  have hLsmall : h < sL * hM * (AL ^ 5 / 200) :=
    (morseAdjacentJoin_quarter_small hsL hAL hAL₀
      (morseAdjacentJoin_quarter_le ha.le hc₁ hsL.le haL hU.le hUL)).1
  have hRsmall : h < sR * hM * (AR / 5) :=
    (morseAdjacentJoin_quarter_small hsR hAR hAR₀
      (morseAdjacentJoin_quarter_le ha.le hc₁ hsR.le haR hU.le hUR)).2
  have hLwidth := morseAdjacentJoin_scaled_increment hrL hsL.le hxL.2.le
    (fun x hx => (hLc x hx).2.2.1)
  rw [show qL - eL = hM by dsimp only [qL]; ring] at hLwidth
  have hRwidth := morseAdjacentJoin_scaled_increment hrR hsR.le hxR.1.le
    (fun x hx => (hRc x hx).2.2.1)
  rw [show morseCellLeftCut - p = hM by dsimp only [p]; ring] at hRwidth
  have hLin : a + h < sL * rL qL := by
    have hw : sL * hM * (AL ^ 5 / 200) ≤ sL * rL qL - a := hLwidth
    linarith only [hw, hLsmall]
  have hRin : sR * rR p < b - h := by
    have hw : sR * hM * (AR / 5) ≤ b - sR * rR p := hRwidth
    linarith only [hw, hRsmall]
  have hLamL : 0 < lamL := morseChainAmplitude_pos T σ hσ n
  have hLamR : 0 < lamR := morseChainAmplitude_pos T σ hσ m
  have hm : 0 < floor := div_pos (by norm_num) ha
  have hFloorL : floor ≤ (100 / (9 : ℝ) ^ 9) / (sL * AL) :=
    morseAdjacentJoin_floor ha hsL hAL (by linarith only [haL₀, hsL]) hALs
  have hFloorR : floor ≤ (100 / (9 : ℝ) ^ 9) / (sR * AR) :=
    morseAdjacentJoin_floor ha hsR hAR haR₀ hARs
  have hmonoL := morseAdjacentJoin_scaled_mono hsL hrL hvL
  have hmonoR := morseAdjacentJoin_scaled_mono hsR hrR hvR
  have hSlopeL (x : ℝ) (hx : x ∈ Ioo p qL) (hy : sL * rL x ∈ Icc a (a + h)) :
      floor ≤ -morseRho AL BL x * rL x / (sL * (deriv rL x) ^ 2) ∧
        -morseRho AL BL x * rL x / (sL * (deriv rL x) ^ 2) ≤ KL := by
    have hxe : eL ≤ x := by
      by_contra hbad
      exact (not_lt_of_ge hy.1) (hmonoL hx hxL (lt_of_not_ge hbad))
    obtain ⟨hr₁, hr₂, hv₁, hv₂, hρ₁, hρ₂⟩ := hLc x ⟨hxe, hx.2.le⟩
    have hs := morseCollarLogSlope_bounds hAL hBL hsL hBAL.1 hBAL.2 ⟨hr₁, hr₂⟩
      (Or.inr ⟨hv₁, hv₂, hρ₁, hρ₂⟩)
    exact ⟨hFloorL.trans hs.1, hs.2⟩
  have hSlopeR (x : ℝ) (hx : x ∈ Ioo p qR) (hy : sR * rR x ∈ Icc (b - h) b) :
      floor ≤ -morseRho AR BR x * rR x / (sR * (deriv rR x) ^ 2) ∧
        -morseRho AR BR x * rR x / (sR * (deriv rR x) ^ 2) ≤ KR := by
    have hxc : x ≤ morseCellLeftCut := by
      by_contra hbad
      exact (not_lt_of_ge hy.2) (hmonoR hxR hx (lt_of_not_ge hbad))
    obtain ⟨hr₁, hr₂, hv₁, hv₂, hρ₁, hρ₂⟩ := hRc x ⟨hx.1.le, hxc⟩
    have hs := morseCollarLogSlope_bounds hAR hBR hsR hBAR.1 hBAR.2 ⟨hr₁, hr₂⟩
      (Or.inl ⟨hv₁, hv₂, hρ₁, hρ₂⟩)
    exact ⟨hFloorR.trans hs.1, hs.2⟩
  have himL := morseCollar_scaledRadius_image_Ioo hpqL hsL hrL hvL
  have himR := morseCollar_scaledRadius_image_Ioo hpqR hsR hrR hvR
  have haIn : a ∈ Ioo (sL * rL p) (sL * rL qL) := by
    rw [← himL]
    exact ⟨eL, hxL, rfl⟩
  have hbIn : b ∈ Ioo (sR * rR p) (sR * rR qR) := by
    rw [← himR]
    exact ⟨morseCellLeftCut, hxR, rfl⟩
  obtain ⟨leftExt, hGL, _, hGLg, hGLd⟩ := exists_morseCollarLogProfile_extension
    (p := a) (q := a + h) hpqL hLamL hsL hrL hvL hEqL haIn.1 (le_add_of_nonneg_right hh.le) hLin
  obtain ⟨rightExt, hGR, _, hGRg, hGRd⟩ := exists_morseCollarLogProfile_extension
    (p := b - h) (q := b) hpqR hLamR hsR hrR hvR hEqR hRin (sub_le_self _ hh.le) hbIn.2
  have hGLupper (y : ℝ) (hy : y ∈ Icc a (a + h)) : deriv leftExt y ≤ KL := by
    have hmem : y ∈ (fun x => sL * rL x) '' Ioo p qL := by
      rw [himL]
      exact ⟨haIn.1.trans_le hy.1, hy.2.trans_lt hLin⟩
    obtain ⟨x, hx, rfl⟩ := hmem
    rw [(hGLd x hx hy).deriv]
    exact (hSlopeL x hx hy).2
  have hGRupper (y : ℝ) (hy : y ∈ Icc (b - h) b) : deriv rightExt y ≤ KR := by
    have hmem : y ∈ (fun x => sR * rR x) '' Ioo p qR := by
      rw [himR]
      exact ⟨hRin.trans_le hy.1, hy.2.trans_lt hbIn.2⟩
    obtain ⟨x, hx, rfl⟩ := hmem
    rw [(hGRd x hx hy).deriv]
    exact (hSlopeR x hx hy).2
  have hn₁ : 1 ≤ n := by omega
  have hcontrast := morseJoin_height_log_contrast T σ hσ hn₁ hNn hNm hadj hdn hdm
    hsL hsR hslog hvEndL hvEndR
  obtain ⟨hWL, hWR, _, hrange⟩ := hcontrast
  have hfLa : fL a = log (lamL * sL * deriv rL eL) :=
    morseCollarLogProfile_at_model hsL hrL hvL hxL
  have hfRb : fR b = log (lamR * sR * deriv rR morseCellLeftCut) :=
    morseCollarLogProfile_at_model hsR hrR hvR hxR
  have hWL' : 0 < lamL * sL * deriv rL eL := hWL
  have hWR' : 0 < lamR * sR * deriv rR morseCellLeftCut := hWR
  have hdiff : 2 * (n : ℝ) ^ 2 ≤ fR b - fL a := by
    rw [hfRb, hfLa, ← log_div hWR'.ne' hWL'.ne']
    exact (hrange hn).1
  have hbudgetNum := morseAdjacentJoin_budget_lt_one ha hc hc₁ hsL hsR hAL hAR haL haR
    hU hUL hUR (hUL.trans hAL₀)
  have hbudgetLt : (KL + KR + floor) * ell < 1 := hbudgetNum.1.trans_lt hbudgetNum.2
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hnr 2
  have hgap : (KL + KR + floor) * (b - a) ≤ rightExt b - leftExt a := by
    rw [hwidth, (hGRg b ⟨sub_le_self _ hh.le, le_rfl⟩).eq_of_nhds,
      (hGLg a ⟨le_rfl, le_add_of_nonneg_right hh.le⟩).eq_of_nhds]
    exact hbudgetLt.le.trans ((show (1 : ℝ) ≤ 2 * (n : ℝ) ^ 2 by linarith only [hnsq]).trans hdiff)
  have hbudgetExt := morseJoinBudget_of_upper_slopes hh hh hsep hGL hGR hm.le
    (by positivity : 0 ≤ KL) (by positivity : 0 ≤ KR) hGLupper hGRupper hgap
  have hbudget : MorseJoinBudget a b h h floor fL fR :=
    (morseJoinBudget_congr_of_germs hab.le hh hh hGLg hGRg).mp hbudgetExt
  obtain ⟨FL, FR, hFL, hFR, _, _, hFLg, hFRg, hB, _, hws, _, _, hWa, hWb, hDeriv, _, hwpos, _, hStrict⟩ :=
    exists_morseJoin_of_model_germs hLamL hsL hrL hvL hEqL hxL hLamR hsR hrR hvR hEqR hxR
      hh hh hLin hRin hsep hm.le (fun x hx hy => (hSlopeL x hx hy).1)
      (fun x hx hy => (hSlopeR x hx hy).1) hbudget
  refine ⟨FL, FR, hFL, hFR, hFLg, hFRg, hB, hws, hwpos, hWa, hWb, ?_, hStrict hm⟩
  intro y hy
  calc
    2 / y ≤ floor := div_le_div_of_nonneg_left (by norm_num) ha hy.1
    _ ≤ _ := (le_div_iff₀ (hwpos y)).mpr (hDeriv y hy).2

/-- The adjacent join with its endpoint germs and geometric slope bound. -/
theorem exists_morseAdjacentJoin (T : Statements.MorseChainData) (σ : ℕ → ℝ)
    (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2) {n m : ℕ} (hn : 100 ≤ n)
    (hNn : T.index ≤ n) (hNm : T.index ≤ m) (hadj : m = n + 1 ∨ n = m + 1)
    (hdn : T.d n = morseChainInteger n) (hdm : T.d m = morseChainInteger m)
    {c sL sR : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hsL : 0 < sL) (hsR : 0 < sR)
    {rL rR : ℝ → ℝ} (hrL : ContDiff ℝ ∞ rL) (hrR : ContDiff ℝ ∞ rR) :
    let AL := Statements.morseChainA T n
    let BL := Statements.morseChainB T n
    let AR := Statements.morseChainA T m
    let BR := Statements.morseChainB T m
    let p := morseCellLeftCut - morseJoinCollarWidth
    let eL := morseRightCapEnd AL BL (1 / 100)
    let qL := eL + morseJoinCollarWidth
    let qR := morseRightCapEnd AR BR (1 / 100) + morseJoinCollarWidth
    let a := sL * rL eL
    let b := sR * rR morseCellLeftCut
    let ell := c * a * (min AL AR) ^ 12
    let h := ell / 4
    (∀ x ∈ Ioo p qL, 0 < deriv rL x) →
    (∀ x ∈ Ioo p qR, 0 < deriv rR x) →
    (∀ x ∈ Ioo p qL, deriv (deriv rL) x = -morseRho AL BL x * rL x) →
    (∀ x ∈ Ioo p qR, deriv (deriv rR) x = -morseRho AR BR x * rR x) →
    (∀ x ∈ Icc eL qL,
      (1 / 2 : ℝ) ≤ rL x ∧ rL x ≤ 2 ∧ AL ^ 5 / 200 ≤ deriv rL x ∧
      deriv rL x ≤ AL ^ 5 / 25 ∧ BL / 2 ≤ -morseRho AL BL x ∧ -morseRho AL BL x ≤ BL) →
    (∀ x ∈ Icc p morseCellLeftCut,
      (1 / 2 : ℝ) ≤ rR x ∧ rR x ≤ 2 ∧ AR / 5 ≤ deriv rR x ∧ deriv rR x ≤ 8 * AR ∧
      (3 / 4 : ℝ) * AR ≤ -morseRho AR BR x ∧ -morseRho AR BR x ≤ 7 * AR) →
    ((1 / 100 : ℝ) * AL ^ 5 ≤ deriv rL eL ∧ deriv rL eL ≤ (3 / 100 : ℝ) * AL ^ 5) →
    (AR / 4 ≤ deriv rR morseCellLeftCut ∧ deriv rR morseCellLeftCut ≤ 7 * AR) →
    b - a = ell →
    ∃ FL FR : ℝ → ℝ, ContDiff ℝ ∞ FL ∧ ContDiff ℝ ∞ FR ∧
      MorseJoinBudget a b h h (2 / a) FL FR ∧
      let w := morseJoinProfile a b h h FL FR
      ContDiff ℝ ∞ w ∧ (∀ y, 0 < w y) ∧
      (w =ᶠ[𝓝 a] fun y => Statements.morseChainAmplitude T σ n * sL *
        deriv rL (morseCollarCoordinate rL sL p qL y)) ∧
      (w =ᶠ[𝓝 b] fun y => Statements.morseChainAmplitude T σ m * sR *
        deriv rR (morseCollarCoordinate rR sR p qR y)) ∧
      (∀ y ∈ Icc a b, 2 / y ≤ deriv w y / w y) ∧ StrictMonoOn w (Icc a b) := by
  dsimp only
  intro hvL hvR hEqL hEqR hLc hRc hvEndL hvEndR hPlace
  obtain ⟨FL, FR, hFL, hFR, _, _, hB, hws, hwpos, hWa, hWb, hSlope, hMono⟩ :=
    exists_morseAdjacentJoin_with_model_germs T σ hσ hn hNn hNm hadj hdn hdm hc hc₁ hsL hsR hrL hrR
      hvL hvR hEqL hEqR hLc hRc hvEndL hvEndR hPlace
  exact ⟨FL, FR, hFL, hFR, hB, hws, hwpos, hWa, hWb, hSlope, hMono⟩

end ContinuousFlexibility.Radial
