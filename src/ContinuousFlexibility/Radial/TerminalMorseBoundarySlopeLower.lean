import ContinuousFlexibility.Radial.TerminalMorseSourceNormalization

/-!
# A lower bound for the same terminal stand-in slope

The positive potential makes the actual pulled-back solution convex.
Its fixed endpoint values give a secant lower bound at the normalized
endpoint. The actual cap length, radius, and speed then give a uniform
inverse-power lower bound for the normalized outward slope.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

/-- Both choices of normalized endpoint use the same convexity argument. -/
theorem terminalCap_endpoint_slope_lower (right : Bool) {L : ℝ} {p q : ℝ → ℝ}
    (hL : 0 < L) (hp : ContDiff ℝ ∞ p)
    (heq : ∀ t ∈ Icc 0 L, deriv (deriv p) t = q t * p t)
    (hq : ∀ t ∈ Ioo 0 L, 0 < q t)
    (hzero : p 0 = if right then 0 else 1)
    (hend : p L = if right then 1 else 0) :
    1 / L ≤ if right then deriv p L else -deriv p 0 := by
  have hp' : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hnonneg : ∀ t ∈ Icc 0 L, 0 ≤ p t := by
    apply positiveBuffer_solution_nonneg hp.continuous.continuousOn
      (fun t _ => (hp.differentiable (by simp) t).hasDerivAt)
      (fun t ht => (heq t (Ioo_subset_Icc_self ht)) ▸
        (hp'.differentiable (by simp) t).hasDerivAt) hq
    · rw [hzero]; cases right <;> norm_num
    · rw [hend]; cases right <;> norm_num
  have hconv : ConvexOn ℝ (Icc 0 L) p := by
    apply convexOn_of_deriv2_nonneg (convex_Icc (0 : ℝ) L) hp.continuous.continuousOn
      (hp.differentiable (by simp)).differentiableOn
      (hp'.differentiable (by simp)).differentiableOn
    intro t ht
    rw [interior_Icc] at ht
    change 0 ≤ deriv (deriv p) t
    rw [heq t (Ioo_subset_Icc_self ht)]
    exact mul_nonneg (hq t ht).le (hnonneg t (Ioo_subset_Icc_self ht))
  cases right
  · have h := hconv.deriv_le_slope ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
      (hp.differentiable (by simp) 0)
    simp only [slope_def_field, hzero, hend, sub_zero, sub_self, zero_sub, zero_div,
      Bool.false_eq_true, if_false] at h
    linarith only [h]
  · have h := hconv.slope_le_deriv ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
      (hp.differentiable (by simp) L)
    simpa only [slope_def_field, hzero, hend, sub_zero, if_true] using h

theorem terminalMorseLayer_cap_point_mem (long : Bool) {A B t : ℝ}
    (ht : t ∈ Icc 0 (terminalMorseLayerLength long A)) :
    terminalMorseLayerOrigin long A B + t ∈
      Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut) := by
  cases long
  · change t ∈ Icc 0 morseShortLeftCapLength at ht
    change morseCellLeftCut + t ∈ Icc morseCellLeftCut morseShortLeftCapCut
    dsimp only [morseShortLeftCapLength] at ht
    constructor <;> linarith only [ht.1, ht.2]
  · change t ∈ Icc 0 (morseRightCapLength A (1 / 100)) at ht
    change morseRightTurn A B + t ∈
      Icc (morseRightTurn A B) (morseRightCapEnd A B (1 / 100))
    dsimp only [morseRightCapEnd]
    constructor <;> linarith only [ht.1, ht.2]

theorem terminalMorseLayerLength_mul_A4_le_one (long : Bool) {A : ℝ}
    (hA : 0 < A) (hA₁ : A ≤ 1) :
    terminalMorseLayerLength long A * A ^ 4 ≤ 1 := by
  cases long
  · have hlog₁ : 0 ≤ log (5 / 4 : ℝ) := log_nonneg (by norm_num)
    have hlog₂ := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    have hL : morseShortLeftCapLength ≤ 1 := by
      unfold morseShortLeftCapLength morseShortLeftCapCut morseCellLeftCut
      linarith only [hlog₁, hlog₂]
    have hpow : A ^ 4 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hA.le hA₁ 4
    exact (mul_le_mul hL hpow (pow_nonneg hA.le 4) zero_le_one).trans_eq (one_mul 1)
  · change morseRightCapLength A (1 / 100) * A ^ 4 ≤ 1
    calc
      _ = (1 / 100 : ℝ) := by
        unfold morseRightCapLength
        field_simp [hA.ne'] <;> ring
      _ ≤ _ := by norm_num

/-- The outward slope is that of the input solution itself. Only the
equation on its positive cap is required, not an equation on the full cell. -/
theorem terminalMorse_standIn_slope_lower (long : Bool)
    {A B j s weightScale : ℝ} {r w u : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 0 < j) (hs : 0 < s)
    (hscale : weightScale ≠ 0) (hA₀ : A ≤ 1 / 1000)
    (hr : IsNormalizedMorseCell A B r) (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hode : ∀ x ∈ Icc (if long then morseRightTurn A B else morseCellLeftCut)
        (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut),
      radialJacobi (j ^ 2) w u (s * r x) = 0)
    (hzero : u (s * r (if long then morseRightTurn A B else morseShortLeftCapCut)) = 0)
    (hjoin : u (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) = 1) :
    A ^ 3 / (14 * j ^ 2) ≤ standInBoundarySlope (if long then 1 else -1) (j ^ 2)
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)) u := by
  let R := terminalMorseLayerRadius long A B s r
  let L := terminalMorseLayerLength long A
  let p : ℝ → ℝ := fun t => u (R t)
  let q : ℝ → ℝ := fun t => j ^ 2 * (-morseRho A B (terminalMorseLayerOrigin long A B + t))
  let xi : ℝ := if long then L else 0
  let epsilon : ℝ := if long then 1 else -1
  let g : ℝ := epsilon * deriv p xi
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hR : ContDiff ℝ ∞ R := terminalMorseLayerRadius_smooth long A B s hr.smooth
  have hp : ContDiff ℝ ∞ p := hu.comp hR
  have hweightR (t : ℝ) (ht : t ∈ Icc 0 L) : w (R t) = weightScale * deriv R t := by
    change w (s * r (terminalMorseLayerOrigin long A B + 1 * t)) =
      weightScale * deriv (terminalMorseCapRadius s (terminalMorseLayerOrigin long A B) 1 r) t
    rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth]
    simpa only [one_mul, mul_one] using hweight _ (terminalMorseLayer_point_mem long hB hAB ht)
  have hodeR (t : ℝ) (ht : t ∈ Icc 0 L) : radialJacobi (j ^ 2) w u (R t) = 0 := by
    simpa only [R, terminalMorseLayerRadius, terminalMorseCapRadius, one_mul] using
      hode _ (terminalMorseLayer_cap_point_mem long ht)
  obtain ⟨hfirst, hsecond⟩ := r07_cap_pullback_system hL hscale hR hw hu hweightR hodeR
  have hpd : deriv p = fun t => deriv u (R t) * deriv R t :=
    funext (fun t => ((hu.differentiable (by simp) (R t)).hasDerivAt.comp t
      (hR.differentiable (by simp) t).hasDerivAt).deriv)
  have heq (t : ℝ) (ht : t ∈ Icc 0 L) : deriv (deriv p) t = q t * p t := by
    have hRt : R t ≠ 0 := (terminalMorseLayerRadius_pos long hB hAB hs hr ht).ne'
    have hReq : deriv (deriv R) t =
        -morseRho A B (terminalMorseLayerOrigin long A B + t) * R t :=
      terminalMorseLayerRadius_equation long hB hAB hs hr ht
    calc
      _ = (j ^ 2 * deriv (deriv R) t / R t) * u (R t) := by
        rw [hpd]
        exact (hsecond t ht).deriv
      _ = _ := by
        rw [hReq]
        dsimp only [q, p]
        field_simp [hRt] <;> ring
  have hq (t : ℝ) (ht : t ∈ Ioo 0 L) : 0 < q t := by
    apply mul_pos (sq_pos_of_pos hj)
    apply neg_pos.mpr
    cases long
    · apply morseRho_neg_before_left_turn hB hAB
      have hmem := terminalMorseLayer_cap_point_mem false (A := A) (B := B) (Ioo_subset_Icc_self ht)
      exact hmem.2.trans_lt (morseShortLeftCapCut_lt_leftTurn hB hAB)
    · apply morseRho_neg_after_right_turn hB hAB
      change morseRightTurn A B < morseRightTurn A B + t
      linarith only [ht.1]
  have hR0 : R 0 = s * r (if long then morseRightTurn A B else morseCellLeftCut) := by
    cases long <;> simp [R, terminalMorseLayerRadius, terminalMorseCapRadius, terminalMorseLayerOrigin]
  have hRL : R L = s * r (if long then morseRightCapEnd A B (1 / 100) else morseShortLeftCapCut) := by
    cases long <;> simp [R, L, terminalMorseLayerRadius, terminalMorseCapRadius,
      terminalMorseLayerOrigin, terminalMorseLayerLength, morseRightCapEnd, morseShortLeftCapLength]
  have hp0 : p 0 = if long then 0 else 1 := by
    change u (R 0) = _
    rw [hR0]
    cases long <;> assumption
  have hpL : p L = if long then 1 else 0 := by
    change u (R L) = _
    rw [hRL]
    cases long <;> assumption
  have hgslope : 1 / L ≤ g := by
    have h := terminalCap_endpoint_slope_lower long hL hp heq hq hp0 hpL
    cases long <;> simpa [g, epsilon, xi] using h
  have hximem : xi ∈ Icc 0 L := by cases long <;> exact ⟨by simp [xi, hL.le], by simp [xi, hL.le]⟩
  have hxcell := terminalMorseLayer_point_mem long hB hAB hximem
  have hRlow : s / 2 ≤ R xi := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_radius_lower hA₀ hr hxcell) hs.le
    change s / 2 ≤ s * r (terminalMorseLayerOrigin long A B + 1 * xi)
    simp only [one_mul]
    linarith only [h]
  have hRpos : 0 < R xi := (div_pos hs (by norm_num)).trans_le hRlow
  have hspeed : 0 < deriv R xi := (by positivity : 0 < s * A ^ 5 / 100).trans_le
    (terminalMorseLayerRadius_speed_lower long hB hAB hs hr hximem)
  have hspeedup : deriv R xi ≤ 7 * s * A := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_speed_upper hA hA₀ hr hxcell) hs.le
    change deriv (terminalMorseCapRadius s (terminalMorseLayerOrigin long A B) 1 r) xi ≤ _
    rw [terminalMorseCapRadius_deriv _ _ _ _ hr.smooth]
    simp only [one_mul, mul_one]
    nlinarith only [h]
  have hfrac : 1 / (14 * j ^ 2 * A) ≤ R xi / (j ^ 2 * deriv R xi) := by
    calc
      _ = (s / 2) / (j ^ 2 * (7 * s * A)) := by
        field_simp [hs.ne', hj.ne', hA.ne'] <;> ring
      _ ≤ R xi / (j ^ 2 * (7 * s * A)) :=
        div_le_div_of_nonneg_right hRlow (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hRpos.le (by positivity)
        (mul_le_mul_of_nonneg_left hspeedup (sq_nonneg j))
  have hLbudget : L * A ^ 4 ≤ 1 :=
    terminalMorseLayerLength_mul_A4_le_one long hA (hA₀.trans (by norm_num))
  have hbase : A ^ 3 / (14 * j ^ 2) ≤ (1 / (14 * j ^ 2 * A)) * (1 / L) := by
    calc
      _ = (L * A ^ 4) / (14 * j ^ 2 * A * L) := by
        field_simp [hA.ne', hj.ne', hL.ne'] <;> ring
      _ ≤ 1 / (14 * j ^ 2 * A * L) :=
        div_le_div_of_nonneg_right hLbudget (by positivity)
      _ = _ := by ring
  have hjoinR : R xi = s * r
      (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut) := by
    cases long
    · exact hR0
    · exact hRL
  have hujoin : u (R xi) = 1 := by rw [hjoinR]; exact hjoin
  have hd : standInBoundarySlope epsilon (j ^ 2) (R xi) u =
      R xi / (j ^ 2 * deriv R xi) * g := by
    dsimp only [standInBoundarySlope, g]
    rw [hujoin, congrFun hpd xi]
    field_simp [hj.ne', hspeed.ne'] <;> ring
  change A ^ 3 / (14 * j ^ 2) ≤ standInBoundarySlope epsilon (j ^ 2) _ u
  rw [← hjoinR, hd]
  exact hbase.trans (mul_le_mul hfrac hgslope (one_div_nonneg.mpr hL.le) (by positivity))

theorem terminalCap_sqrt_slope_lower {A j d : ℝ}
    (hA : 0 < A) (hA₁ : A ≤ 1) (hj : 0 < j)
    (hd : A ^ 3 / (14 * j ^ 2) ≤ d) :
    A ^ 2 / (4 * j) ≤ sqrt d := by
  have hp : A ^ 4 ≤ A ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hA₁ (pow_nonneg hA.le 3)
    nlinarith only [h]
  have hsq : (A ^ 2 / (4 * j)) ^ 2 ≤ d := by
    apply le_trans ?_ hd
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : 0 < (4 * j) ^ 2)
      (by positivity : 0 < 14 * j ^ 2)).mpr
    rw [show (A ^ 2) ^ 2 = A ^ 4 by ring]
    nlinarith only [mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 14 * j ^ 2),
      mul_nonneg (pow_nonneg hA.le 3) (sq_nonneg j)]
  simpa only [sqrt_sq (by positivity : 0 ≤ A ^ 2 / (4 * j))] using sqrt_le_sqrt hsq

end ContinuousFlexibility.Radial

