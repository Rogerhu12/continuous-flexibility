import ContinuousFlexibility.Radial.MorseRadiusODE
import ContinuousFlexibility.Radial.MorseChainParameters

/-!
# The long right Morse cap

The Volterra equation controls the deviation of the radius from its
initial value. Once this control gives positivity, the velocity integral
gives the lower and upper speed bounds. The cap length in the radius
coordinate and its travel integral are calculated on the same interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def morseRightCapLength (A c : ℝ) : ℝ := c / A ^ 4

def morseRightCapEnd (A B c : ℝ) : ℝ := morseRightTurn A B + morseRightCapLength A c

def morseRightCapTravel (A B c : ℝ) : ℝ :=
  ∫ y in morseRightTurn A B..morseRightCapEnd A B c, sqrt (-morseRho A B y)

theorem morseRightCapLength_pos {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    0 < morseRightCapLength A c :=
  div_pos hc (pow_pos hA 4)

private theorem morseRightCapLength_mul {A c : ℝ} (hA : 0 < A) :
    morseRightCapLength A c * A ^ 4 = c :=
  div_mul_cancel₀ _ (pow_ne_zero _ hA.ne')

private theorem abs_right_volterra_integral_le {x₀ x B M : ℝ} {ρ r : ℝ → ℝ}
    (h : x₀ ≤ x) (hB : 0 ≤ B) (hρc : Continuous ρ) (hrc : Continuous r)
    (hρ : ∀ y ∈ Icc x₀ x, |ρ y| ≤ B) (hr : ∀ y ∈ Icc x₀ x, |r y| ≤ M) :
    |∫ y in x₀..x, (x - y) * ρ y * r y| ≤ B * M * (x - x₀) ^ 2 / 2 := by
  have hgap : Continuous (fun y : ℝ => x - y) := continuous_const.sub continuous_id
  have hker : Continuous (fun y : ℝ => (x - y) * ρ y * r y) := (hgap.mul hρc).mul hrc
  have hmaj : Continuous (fun y : ℝ => (B * M) * (x - y)) := continuous_const.mul hgap
  have hpt (y : ℝ) (hy : y ∈ Icc x₀ x) :
      |(x - y) * ρ y * r y| ≤ (B * M) * (x - y) := by
    have hxy : 0 ≤ x - y := sub_nonneg.mpr hy.2
    simp only [abs_mul, abs_of_nonneg hxy]
    calc
      (x - y) * |ρ y| * |r y| = (x - y) * (|ρ y| * |r y|) := mul_assoc _ _ _
      _ ≤ (x - y) * (B * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hρ y hy) (hr y hy) (abs_nonneg _) hB) hxy
      _ = (B * M) * (x - y) := mul_comm _ _
  have hprim : (∫ y in x₀..x, x - y) = (x - x₀) ^ 2 / 2 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => x) volume x₀ x :=
      continuous_const.intervalIntegrable x₀ x
    have hid : IntervalIntegrable (fun y : ℝ => y) volume x₀ x :=
      continuous_id.intervalIntegrable x₀ x
    rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  calc
    |∫ y in x₀..x, (x - y) * ρ y * r y| ≤ ∫ y in x₀..x, |(x - y) * ρ y * r y| :=
      intervalIntegral.abs_integral_le_integral_abs h
    _ ≤ ∫ y in x₀..x, (B * M) * (x - y) :=
      intervalIntegral.integral_mono_on h (hker.abs.intervalIntegrable x₀ x)
        (hmaj.intervalIntegrable x₀ x) hpt
    _ = B * M * (x - x₀) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, hprim]
      ring

/-- The prescribed initial data give an increasing radius on the whole
long right cap. The deviation estimate is obtained before using positivity. -/
theorem morseRightCap_radius_bounds {A B δ c : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hA₁ : A ≤ 1) (hBA : B ≤ A ^ 9)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 4) (hc : 0 < c) (hc₁ : c ≤ 1 / 4)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hr₀ : r (morseRightTurn A B) = 1) (hv₀ : deriv r (morseRightTurn A B) = δ * A ^ 5)
    (hEq : ∀ y ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B c),
      deriv (deriv r) y = -morseRho A B y * r y) :
    ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B c),
      |r x - 1| ≤ (2 * δ * c + c ^ 2) * A ∧ 0 < r x ∧ r x ≤ 2 ∧
        δ * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (δ + 2 * c) * A ^ 5 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let x₀ := morseRightTurn A B
  let T := morseRightCapLength A c
  let e := x₀ + T
  change ∀ y ∈ Icc x₀ e, deriv (deriv r) y = -morseRho A B y * r y at hEq
  change ∀ x ∈ Icc x₀ e, |r x - 1| ≤ (2 * δ * c + c ^ 2) * A ∧ 0 < r x ∧ r x ≤ 2 ∧
    δ * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (δ + 2 * c) * A ^ 5
  have hT : 0 ≤ T := (morseRightCapLength_pos hA hc).le
  have hTA : T * A ^ 4 = c := morseRightCapLength_mul hA
  have hstart : x₀ ∈ Icc x₀ e := ⟨le_rfl, le_add_of_nonneg_right hT⟩
  have hvpos : 0 ≤ δ * A ^ 5 := mul_nonneg hδ.le (pow_nonneg hA.le _)
  have hc₂ : c ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hc.le hc₁ 2
  have hδc : δ * c ≤ (1 / 4 : ℝ) * (1 / 4) := mul_le_mul hδ₁ hc₁ hc.le (by norm_num)
  let D := (δ * A ^ 5) * T
  let η := B * T ^ 2 / 2
  have hD : D = δ * c * A := calc
    D = δ * (T * A ^ 4) * A := by dsimp only [D]; ring
    _ = _ := by rw [hTA]
  have hη : η ≤ c ^ 2 / 2 * A := calc
    η ≤ A ^ 9 * T ^ 2 / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBA (sq_nonneg T)) (by norm_num)
    _ = (T * A ^ 4) ^ 2 / 2 * A := by ring
    _ = _ := by rw [hTA]
  have hηsmall : η ≤ 1 / 2 := calc
    η ≤ c ^ 2 / 2 * A := hη
    _ ≤ (1 / 32 : ℝ) * A :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hc₂]) hA.le
    _ ≤ (1 / 32 : ℝ) * 1 := mul_le_mul_of_nonneg_left hA₁ (by norm_num)
    _ ≤ _ := by norm_num
  obtain ⟨p, hp, hpmax⟩ := (isCompact_Icc : IsCompact (Icc x₀ e)).exists_isMaxOn
    ⟨x₀, hstart⟩ ((hr.continuous.sub continuous_const).abs.continuousOn)
  let M := |r p - 1|
  have hM₀ : 0 ≤ M := abs_nonneg _
  have hM (x : ℝ) (hx : x ∈ Icc x₀ e) : |r x - 1| ≤ M := isMaxOn_iff.mp hpmax x hx
  have hrabs (x : ℝ) (hx : x ∈ Icc x₀ e) : |r x| ≤ 1 + M := calc
    |r x| = |(r x - 1) + 1| := by rw [sub_add_cancel]
    _ ≤ |r x - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 1 + M := by
      rw [abs_one, add_comm (|r x - 1|) 1]
      exact add_le_add_right (hM x hx) 1
  have hρ (x : ℝ) (hx : x₀ ≤ x) : |morseRho A B x| ≤ B := by
    have h := morseRho_right_cap_bounds hB hAB hx
    rw [abs_of_nonpos (neg_nonneg.mp h.1)]
    exact h.2
  have hdev (x : ℝ) (hx : x ∈ Icc x₀ e) : |r x - 1| ≤ D + η * (1 + M) := by
    have hdx : x - x₀ ≤ T := by
      have he : x ≤ x₀ + T := hx.2
      linarith only [he]
    have hsub : Icc x₀ x ⊆ Icc x₀ e := Icc_subset_Icc_right hx.2
    let I : ℝ := ∫ y in x₀..x, (x - y) * morseRho A B y * r y
    have hI : |I| ≤ η * (1 + M) := calc
      |I| ≤ B * (1 + M) * (x - x₀) ^ 2 / 2 :=
        abs_right_volterra_integral_le hx.1 hB.le (contDiff_morseRho A B).continuous hr.continuous
          (fun y hy => hρ y hy.1) (fun y hy => hrabs y (hsub hy))
      _ ≤ B * (1 + M) * T ^ 2 / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hx.1) hdx 2)
            (mul_nonneg hB.le (add_nonneg zero_le_one hM₀))) (by norm_num)
      _ = η * (1 + M) := by dsimp only [η]; ring
    have hR := morseRadius_eq_volterra hr hstart hx hEq
    change r x = r x₀ + deriv r x₀ * (x - x₀) - I at hR
    have h0 : r x₀ = 1 := hr₀
    have hv : deriv r x₀ = δ * A ^ 5 := hv₀
    rw [h0, hv] at hR
    have he : r x - 1 = (δ * A ^ 5) * (x - x₀) - I := by linarith only [hR]
    have hab := abs_sub_le ((δ * A ^ 5) * (x - x₀)) 0 I
    rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hvpos (sub_nonneg.mpr hx.1))] at hab
    rw [he]
    exact hab.trans (add_le_add (mul_le_mul_of_nonneg_left hdx hvpos) hI)
  have hMp : M ≤ D + η * (1 + M) := hdev p hp
  have hηM : η * M ≤ (1 / 2 : ℝ) * M := mul_le_mul_of_nonneg_right hηsmall hM₀
  have hMclose : M ≤ (2 * δ * c + c ^ 2) * A := calc
    M ≤ 2 * (D + η) := by nlinarith only [hMp, hηM]
    _ ≤ _ := by nlinarith only [hD, hη]
  have hcoef : 2 * δ * c + c ^ 2 ≤ (3 / 16 : ℝ) := by nlinarith only [hδc, hc₂]
  have hclose (x : ℝ) (hx : x ∈ Icc x₀ e) : |r x - 1| ≤ (2 * δ * c + c ^ 2) * A :=
    (hM x hx).trans hMclose
  have hrange (x : ℝ) (hx : x ∈ Icc x₀ e) : 0 < r x ∧ r x ≤ 2 := by
    have h : |r x - 1| ≤ 3 / 16 := calc
      _ ≤ (2 * δ * c + c ^ 2) * A := hclose x hx
      _ ≤ (3 / 16 : ℝ) * A := mul_le_mul_of_nonneg_right hcoef hA.le
      _ ≤ (3 / 16 : ℝ) * 1 := mul_le_mul_of_nonneg_left hA₁ (by norm_num)
      _ = _ := mul_one _
    exact ⟨by linarith only [(abs_le.mp h).1], by linarith only [(abs_le.mp h).2]⟩
  have hBT : B * T ≤ c * A ^ 5 := calc
    _ ≤ A ^ 9 * T := mul_le_mul_of_nonneg_right hBA hT
    _ = (T * A ^ 4) * A ^ 5 := by ring
    _ = _ := by rw [hTA]
  intro x hx
  have hsub : Icc x₀ x ⊆ Icc x₀ e := Icc_subset_Icc_right hx.2
  let f : ℝ → ℝ := fun y => -morseRho A B y * r y
  have hf : Continuous f := (contDiff_morseRho A B).continuous.neg.mul hr.continuous
  have hf0 : 0 ≤ ∫ y in x₀..x, f y :=
    intervalIntegral.integral_nonneg hx.1 fun y hy =>
      mul_nonneg (morseRho_right_cap_bounds hB hAB hy.1).1 (hrange y (hsub hy)).1.le
  have hfupper : (∫ y in x₀..x, f y) ≤ ∫ _ in x₀..x, 2 * B :=
    intervalIntegral.integral_mono_on hx.1 (hf.intervalIntegrable x₀ x)
      ((continuous_const : Continuous (fun _ : ℝ => 2 * B)).intervalIntegrable x₀ x)
      (fun y hy => by
        have h := morseRho_right_cap_bounds hB hAB hy.1
        exact (mul_le_mul h.2 (hrange y (hsub hy)).2 (hrange y (hsub hy)).1.le hB.le).trans_eq
          (mul_comm _ _))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hfupper
  have hdx : x - x₀ ≤ T := by
    have he : x ≤ x₀ + T := hx.2
    linarith only [he]
  have hfbd : (∫ y in x₀..x, f y) ≤ 2 * c * A ^ 5 := calc
    _ ≤ (x - x₀) * (2 * B) := hfupper
    _ ≤ T * (2 * B) := mul_le_mul_of_nonneg_right hdx (by positivity)
    _ = 2 * (B * T) := by ring
    _ ≤ 2 * (c * A ^ 5) := mul_le_mul_of_nonneg_left hBT (by norm_num)
    _ = _ := by ring
  have hneg : (∫ y in x₀..x, f y) = -(∫ y in x₀..x, morseRho A B y * r y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    change -morseRho A B y * r y = -(morseRho A B y * r y)
    ring
  have hv := morseRadius_velocity_eq_integral hr hstart hx hEq
  change deriv r x = deriv r x₀ - ∫ y in x₀..x, morseRho A B y * r y at hv
  have hvstart : deriv r x₀ = δ * A ^ 5 := hv₀
  rw [hvstart, sub_eq_add_neg, ← hneg] at hv
  refine ⟨hclose x hx, (hrange x hx).1, (hrange x hx).2, ?_, ?_⟩
  · rw [hv]
    exact le_add_of_nonneg_right hf0
  · nlinarith only [hv, hfbd]

/-- The radius-coordinate length of the same cap has two-sided bounds
linear in the parameter `A`. -/
theorem morseRightCap_radius_span {A B δ c : ℝ} (hA : 0 < A) (hc : 0 < c)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r)
    (hv : ∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B c),
      δ * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (δ + 2 * c) * A ^ 5) :
    δ * c * A ≤ r (morseRightCapEnd A B c) - r (morseRightTurn A B) ∧
      r (morseRightCapEnd A B c) - r (morseRightTurn A B) ≤ (δ + 2 * c) * c * A := by
  let x₀ := morseRightTurn A B
  let T := morseRightCapLength A c
  let e := x₀ + T
  change ∀ x ∈ Icc x₀ e, δ * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (δ + 2 * c) * A ^ 5 at hv
  change δ * c * A ≤ r e - r x₀ ∧ r e - r x₀ ≤ (δ + 2 * c) * c * A
  have hxe : x₀ ≤ e := le_add_of_nonneg_right (morseRightCapLength_pos hA hc).le
  have hTA : T * A ^ 4 = c := morseRightCapLength_mul hA
  have hscale (d : ℝ) : (e - x₀) * (d * A ^ 5) = d * c * A := calc
    _ = d * (T * A ^ 4) * A := by dsimp only [e]; ring
    _ = _ := by rw [hTA]
  have hi : IntervalIntegrable (deriv r) volume x₀ e :=
    (contDiff_infty_iff_deriv.mp hr).2.continuous.intervalIntegrable x₀ e
  have hFTC : (∫ x in x₀..e, deriv r x) = r e - r x₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hr.differentiable (by simp) x).hasDerivAt) hi
  have hlo : (∫ _ in x₀..e, δ * A ^ 5) ≤ ∫ x in x₀..e, deriv r x :=
    intervalIntegral.integral_mono_on hxe
      ((continuous_const : Continuous (fun _ : ℝ => δ * A ^ 5)).intervalIntegrable x₀ e)
      hi (fun x hx => (hv x hx).1)
  have hhi : (∫ x in x₀..e, deriv r x) ≤ ∫ _ in x₀..e, (δ + 2 * c) * A ^ 5 :=
    intervalIntegral.integral_mono_on hxe hi
      ((continuous_const : Continuous (fun _ : ℝ => (δ + 2 * c) * A ^ 5)).intervalIntegrable x₀ e)
      (fun x hx => (hv x hx).2)
  rw [hFTC, intervalIntegral.integral_const, smul_eq_mul, hscale] at hlo hhi
  exact ⟨hlo, hhi⟩

private theorem morseRightCap_travel_bounds_length {A B T : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) (hT : 2 * log 4 ≤ T) :
    T / 2 * sqrt (B / 2) ≤
      (∫ y in morseRightTurn A B..morseRightTurn A B + T, sqrt (-morseRho A B y)) ∧
    (∫ y in morseRightTurn A B..morseRightTurn A B + T, sqrt (-morseRho A B y)) ≤
      T * sqrt B := by
  let xR := morseRightTurn A B
  let m := xR + log 4
  let e := xR + T
  let f : ℝ → ℝ := fun y => sqrt (-morseRho A B y)
  change T / 2 * sqrt (B / 2) ≤ (∫ y in xR..e, f y) ∧ (∫ y in xR..e, f y) ≤ T * sqrt B
  have hf : Continuous f := (contDiff_morseRho A B).continuous.neg.sqrt
  have hlog : 0 ≤ log 4 := (log_pos (by norm_num : (1 : ℝ) < 4)).le
  have hxm : xR ≤ m := le_add_of_nonneg_right hlog
  have hme : m ≤ e := by dsimp only [m, e]; linarith only [hlog, hT]
  have hxe : xR ≤ e := hxm.trans hme
  have htail : e - m = T - log 4 := by dsimp only [e, m]; ring
  have hspan : e - xR = T := by dsimp only [e]; ring
  have hcl : Continuous (fun _ : ℝ => sqrt (B / 2)) := continuous_const
  have hcu : Continuous (fun _ : ℝ => sqrt B) := continuous_const
  have hlo : (∫ _ in m..e, sqrt (B / 2)) ≤ ∫ y in m..e, f y :=
    intervalIntegral.integral_mono_on hme (hcl.intervalIntegrable m e) (hf.intervalIntegrable m e)
      (fun y hy => sqrt_le_sqrt (morseRho_right_cap_lower hB hAB hy.1))
  rw [intervalIntegral.integral_const, smul_eq_mul, htail] at hlo
  have hhi : (∫ y in xR..e, f y) ≤ ∫ _ in xR..e, sqrt B :=
    intervalIntegral.integral_mono_on hxe (hf.intervalIntegrable xR e) (hcu.intervalIntegrable xR e)
      (fun y hy => sqrt_le_sqrt (morseRho_right_cap_bounds hB hAB hy.1).2)
  rw [intervalIntegral.integral_const, smul_eq_mul, hspan] at hhi
  have hfirst : 0 ≤ ∫ y in xR..m, f y :=
    intervalIntegral.integral_nonneg hxm (fun y _ => sqrt_nonneg (-morseRho A B y))
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable xR m) (hf.intervalIntegrable m e)
  refine ⟨?_, hhi⟩
  calc
    T / 2 * sqrt (B / 2) ≤ (T - log 4) * sqrt (B / 2) :=
      mul_le_mul_of_nonneg_right (by linarith only [hT]) (sqrt_nonneg _)
    _ ≤ ∫ y in m..e, f y := hlo
    _ ≤ ∫ y in xR..e, f y := by rw [← hadd]; exact le_add_of_nonneg_left hfirst

/-- The actual right-cap travel integral is comparable to `sqrt A`
with explicit constants independent of the cell parameters. -/
theorem morseRightCap_travel_bounds {A B c : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) (hc : 0 < c)
    (hT : 2 * log 4 ≤ morseRightCapLength A c) :
    (c / 2 / sqrt (2 * (9 : ℝ) ^ 9)) * sqrt A ≤ morseRightCapTravel A B c ∧
      morseRightCapTravel A B c ≤ c * sqrt A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let T := morseRightCapLength A c
  let k := sqrt (2 * (9 : ℝ) ^ 9)
  have hT₀ : 0 ≤ T := (morseRightCapLength_pos hA hc).le
  have hTA : T * A ^ 4 = c := morseRightCapLength_mul hA
  have hS : sqrt (A ^ 9) = A ^ 4 * sqrt A := by
    rw [show A ^ 9 = (A ^ 4) ^ 2 * A by ring, sqrt_mul (sq_nonneg _),
      sqrt_sq (pow_nonneg hA.le 4)]
  have hArg : A ^ 9 / (2 * (9 : ℝ) ^ 9) ≤ B / 2 := calc
    _ = (A ^ 9 / (9 : ℝ) ^ 9) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hBAlo (by norm_num)
  have hslo : A ^ 4 * sqrt A / k ≤ sqrt (B / 2) := by
    have h := sqrt_le_sqrt hArg
    rw [sqrt_div (pow_nonneg hA.le 9), hS] at h
    exact h
  have hshi : sqrt B ≤ A ^ 4 * sqrt A := (sqrt_le_sqrt hBAhi).trans_eq hS
  obtain ⟨hlo, hhi⟩ := morseRightCap_travel_bounds_length hB hAB hT
  change T / 2 * sqrt (B / 2) ≤ morseRightCapTravel A B c at hlo
  change morseRightCapTravel A B c ≤ T * sqrt B at hhi
  change (c / 2 / k) * sqrt A ≤ morseRightCapTravel A B c ∧
    morseRightCapTravel A B c ≤ c * sqrt A
  constructor
  · calc
      (c / 2 / k) * sqrt A = (T * A ^ 4 / 2 / k) * sqrt A := by rw [hTA]
      _ = T / 2 * (A ^ 4 * sqrt A / k) := by ring
      _ ≤ T / 2 * sqrt (B / 2) := mul_le_mul_of_nonneg_left hslo (div_nonneg hT₀ (by norm_num))
      _ ≤ _ := hlo
  · calc
      morseRightCapTravel A B c ≤ T * sqrt B := hhi
      _ ≤ T * (A ^ 4 * sqrt A) := mul_le_mul_of_nonneg_left hshi hT₀
      _ = (T * A ^ 4) * sqrt A := by ring
      _ = _ := by rw [hTA]

/-- The fixed cap scale `c = 1/100` is long enough once `A ≤ 1/10`. -/
theorem morseRightCap_travel_bounds_fixed {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hA₁ : A ≤ 1 / 10) (hBAlo : A ^ 9 / (9 : ℝ) ^ 9 ≤ B) (hBAhi : B ≤ A ^ 9) :
    ((1 / 100 : ℝ) / 2 / sqrt (2 * (9 : ℝ) ^ 9)) * sqrt A ≤ morseRightCapTravel A B (1 / 100) ∧
      morseRightCapTravel A B (1 / 100) ≤ (1 / 100 : ℝ) * sqrt A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hpow : A ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ hA.le hA₁ 4
  have h100 : (100 : ℝ) ≤ morseRightCapLength A (1 / 100) := by
    unfold morseRightCapLength
    apply (le_div_iff₀ (pow_pos hA 4)).mpr
    calc
      100 * A ^ 4 ≤ 100 * (1 / 10 : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = _ := by norm_num
  have hlog : log (4 : ℝ) ≤ 3 := by
    simpa only [show (4 : ℝ) - 1 = 3 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hT : 2 * log 4 ≤ morseRightCapLength A (1 / 100) :=
    (show 2 * log (4 : ℝ) ≤ 100 by linarith only [hlog]).trans h100
  exact morseRightCap_travel_bounds hB hAB hBAlo hBAhi (by norm_num) hT

/-- A single radius with the fixed initial speed and cap scale solves the
ODE as far left as the requested finite cut and has the stated right-cap bounds. -/
theorem exists_morseRadius_with_rightCap {A B a : ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hA₁ : A ≤ 1) (hBA : B ≤ A ^ 9) (ha : a ≤ morseRightTurn A B) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r (morseRightTurn A B) = 1 ∧
      deriv r (morseRightTurn A B) = (1 / 100 : ℝ) * A ^ 5 ∧
      (∀ x ∈ Icc a (morseRightCapEnd A B (1 / 100)),
        deriv (deriv r) x = -morseRho A B x * r x) ∧
      (∀ x ∈ Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)),
        |r x - 1| ≤ (3 / 10000 : ℝ) * A ∧ 0 < r x ∧ r x ≤ 2 ∧
          (1 / 100 : ℝ) * A ^ 5 ≤ deriv r x ∧ deriv r x ≤ (3 / 100 : ℝ) * A ^ 5) ∧
      (1 / 10000 : ℝ) * A ≤ r (morseRightCapEnd A B (1 / 100)) - 1 ∧
        r (morseRightCapEnd A B (1 / 100)) - 1 ≤ (3 / 10000 : ℝ) * A := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hscale : (0 : ℝ) < 1 / 100 := by norm_num
  have hstart : morseRightTurn A B ∈ Icc a (morseRightCapEnd A B (1 / 100)) :=
    ⟨ha, le_add_of_nonneg_right (morseRightCapLength_pos hA hscale).le⟩
  obtain ⟨r, hr, hr₀, hv₀, hEq⟩ := exists_morseRadius A B hstart 1 ((1 / 100 : ℝ) * A ^ 5)
  have hsub : Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100)) ⊆
      Icc a (morseRightCapEnd A B (1 / 100)) := Icc_subset_Icc_left ha
  have hb := morseRightCap_radius_bounds (δ := (1 / 100 : ℝ)) (c := (1 / 100 : ℝ))
    hB hAB hA₁ hBA hscale (by norm_num) hscale
    (by norm_num) hr hr₀ hv₀ (fun x hx => hEq x (hsub hx))
  have hspan := morseRightCap_radius_span (B := B) (δ := (1 / 100 : ℝ)) (c := (1 / 100 : ℝ))
    hA hscale hr (fun x hx => (hb x hx).2.2.2)
  rw [hr₀] at hspan
  refine ⟨r, hr, hr₀, hv₀, hEq, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [show 2 * (1 / 100 : ℝ) * (1 / 100) + (1 / 100) ^ 2 = 3 / 10000 by norm_num,
      show (1 / 100 : ℝ) + 2 * (1 / 100) = 3 / 100 by norm_num] using hb x hx
  · simpa only [show (1 / 100 : ℝ) * (1 / 100) = 1 / 10000 by norm_num] using hspan.1
  · simpa only [show ((1 / 100 : ℝ) + 2 * (1 / 100)) * (1 / 100) = 3 / 10000 by norm_num]
      using hspan.2

end ContinuousFlexibility.Radial
