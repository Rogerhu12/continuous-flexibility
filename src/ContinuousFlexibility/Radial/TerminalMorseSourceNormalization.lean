module

public import ContinuousFlexibility.Radial.TerminalMorseSourceL2
public import ContinuousFlexibility.Radial.StandInBoundarySlope

/-!
# Scale cancellation in the actual terminal source

The boundary normalization is the actual value j² w/r at the same
normalized endpoint. The physical radius and profile height cancel
against the weighted layer measure. What remains is an explicit fixed
cutoff constant times the sixteenth inverse power of the Morse parameter.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open scoped ContDiff

theorem terminalMorse_retained_radius_lower {A B x : ℝ} {r : ℝ → ℝ}
    (hA₀ : A ≤ 1 / 1000) (hr : IsNormalizedMorseCell A B r)
    (hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100))) :
    (1 / 2 : ℝ) ≤ r x := by
  by_cases ht : x ≤ morseRightTurn A B
  · have h := (abs_le.mp (hr.left_half x ⟨hx.1, ht⟩).1).1
    linarith only [h, hA₀]
  · have h := (abs_le.mp (hr.right_half x ⟨le_of_not_ge ht, hx.2⟩).1).1
    linarith only [h, hA₀]

theorem terminalMorseLayer_coarse_geometry (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hA₀ : A ≤ 1 / 1000)
    (hr : IsNormalizedMorseCell A B r) :
    s / 2 ≤ terminalMorseLayerLeft long A B s r ∧
      s * A ^ 5 / 2400 ≤ terminalMorseLayerRight long A B s r -
        terminalMorseLayerLeft long A B s r ∧
      terminalMorseLayerRight long A B s r -
        terminalMorseLayerLeft long A B s r ≤ 2 * s := by
  let L := terminalMorseLayerLength long A
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hl : terminalMorseLayerOrigin long A B + L / 4 ∈
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) :=
    terminalMorseLayer_point_mem long hB hAB ⟨by linarith only [hL], by linarith only [hL]⟩
  have hh : terminalMorseLayerOrigin long A B + L / 2 ∈
      Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) :=
    terminalMorseLayer_point_mem long hB hAB ⟨by linarith only [hL], by linarith only [hL]⟩
  have ha : s / 2 ≤ terminalMorseLayerLeft long A B s r := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_radius_lower hA₀ hr hl) hs.le
    change s / 2 ≤ s * r (terminalMorseLayerOrigin long A B + 1 * (L / 4))
    simp only [one_mul]
    linarith only [h]
  have hb : terminalMorseLayerRight long A B s r ≤ 2 * s := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_radius_bounds hr hh).2 hs.le
    change s * r (terminalMorseLayerOrigin long A B + 1 * (L / 2)) ≤ 2 * s
    simp only [one_mul]
    nlinarith only [h]
  have hLlo : (1 / 6 : ℝ) ≤ L := by
    cases long
    · exact terminalMorse_short_length_lower
    · exact (by norm_num : (1 / 6 : ℝ) ≤ 100).trans (terminalMorse_long_length_lower hA hA₀)
  have hwidth := terminalMorseLayer_width_lower long hB hAB hs hr
  have hmul := mul_le_mul_of_nonneg_left hLlo (by positivity : 0 ≤ s * A ^ 5 / 400)
  refine ⟨ha, ?_, ?_⟩
  · exact (by nlinarith only [hmul] :
      s * A ^ 5 / 2400 ≤ s * A ^ 5 * L / 400).trans hwidth
  · linarith only [ha, hb, hs]

/-- A lower bound on the actual matching scale, with the physical
radius scale already canceled. -/
theorem terminalMorse_boundary_normalization_lower (long : Bool)
    {A B j s weightScale lam : ℝ} {r w : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hscale : 0 < weightScale)
    (hr : IsNormalizedMorseCell A B r)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (w (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut))) :
    j ^ 2 * weightScale * A ^ 5 / 200 ≤ lam := by
  let x := if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hend : morseCellLeftCut ≤ morseRightCapEnd A B (1 / 100) :=
    (morseCellLeftCut_lt_rightTurn hB hAB).le.trans
      (le_add_of_nonneg_right (morseRightCapLength_pos hA (by norm_num : (0 : ℝ) < 1 / 100)).le)
  have hx : x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)) := by
    cases long
    · exact ⟨le_rfl, hend⟩
    · exact ⟨hend, le_rfl⟩
  have hrpos : 0 < s * r x := mul_pos hs (terminalMorse_retained_radius_bounds hr hx).1
  have hrupper : s * r x ≤ 2 * s := by
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_radius_bounds hr hx).2 hs.le
    nlinarith only [h]
  have hwlower : weightScale * (s * A ^ 5 / 100) ≤ w (s * r x) := by
    rw [hweight x hx]
    have h := mul_le_mul_of_nonneg_left (terminalMorse_retained_speed_lower hr hx)
      (mul_nonneg hscale.le hs.le)
    nlinarith only [h]
  have hwpos : 0 < w (s * r x) :=
    (by positivity : 0 < weightScale * (s * A ^ 5 / 100)).trans_le hwlower
  calc
    _ = (j ^ 2 * (weightScale * (s * A ^ 5 / 100))) / (2 * s) := by
      field_simp [hs.ne'] <;> ring
    _ ≤ (j ^ 2 * w (s * r x)) / (2 * s) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwlower (sq_nonneg j)) (by positivity)
    _ ≤ (j ^ 2 * w (s * r x)) / (s * r x) :=
      div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg j) hwpos.le) hrpos hrupper
    _ = lam := by simpa only [standInBoundaryScale, x] using hnorm.symm

/-- A scalar estimate with completely specified constants. All its
geometric inputs are proved above for the constructed physical layer. -/
theorem terminalCap_normalized_prefactor_bound
    {A j s k lam a d k₁ k₂ : ℝ}
    (hA : 0 < A) (hA₁ : A ≤ 1) (hj : 1 ≤ j) (hs : 0 < s) (hk : 0 < k)
    (ha : s / 2 ≤ a) (hdlo : s * A ^ 5 / 2400 ≤ d) (hdhi : d ≤ 2 * s)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hlam : j ^ 2 * k * A ^ 5 / 200 ≤ lam) :
    ((2 * s) ^ 2 / (12 * (k * (s * A ^ 5 / 100)))) *
      ((2 * (7 * k * s * A) * (k₁ / d) * (600 * j * sqrt A / (s * A ^ 5)) +
        (((2 * k * s * A) / (s * A ^ 5 / 100)) * (k₁ / d) +
          (7 * k * s * A) * (k₂ / d ^ 2)) * 2) / sqrt lam) *
      sqrt ((12 * (7 * k * s * A) / a ^ 2) * d) ≤
        10000000000000 * (1 + k₁ + k₂) / A ^ 16 := by
  let K := 1 + k₁ + k₂
  have hK : 0 ≤ K := by dsimp only [K]; linarith only [hk₁, hk₂]
  have hK₁ : k₁ ≤ K := by dsimp only [K]; linarith only [hk₂]
  have hK₂ : k₂ ≤ K := by dsimp only [K]; linarith only [hk₁]
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hapos : 0 < a := (div_pos hs (by norm_num)).trans_le ha
  have hdpos : 0 < d := (by positivity : 0 < s * A ^ 5 / 2400).trans_le hdlo
  have hlampos : 0 < lam := (by positivity : 0 < j ^ 2 * k * A ^ 5 / 200).trans_le hlam
  have hc₁ : k₁ / d ≤ 2400 * K / (s * A ^ 5) := by
    calc
      _ ≤ K / d := div_le_div_of_nonneg_right hK₁ hdpos.le
      _ ≤ K / (s * A ^ 5 / 2400) :=
        div_le_div_of_nonneg_left hK (by positivity) hdlo
      _ = _ := by field_simp [hs.ne', hA.ne'] <;> ring
  have hd₂ : (s * A ^ 5 / 2400) ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ (by positivity) hdpos.le).mpr hdlo
  have hc₂ : k₂ / d ^ 2 ≤ 5760000 * K / (s ^ 2 * A ^ 10) := by
    calc
      _ ≤ K / d ^ 2 := div_le_div_of_nonneg_right hK₂ (sq_nonneg d)
      _ ≤ K / (s * A ^ 5 / 2400) ^ 2 :=
        div_le_div_of_nonneg_left hK (by positivity) hd₂
      _ = _ := by field_simp [hs.ne', hA.ne'] <;> ring
  have hsqrt : sqrt A ≤ 1 := (sqrt_le_left zero_le_one).mpr (by simpa only [one_pow] using hA₁)
  have hu : 600 * j * sqrt A / (s * A ^ 5) ≤ 600 * j / (s * A ^ 5) := by
    exact div_le_div_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 600 * j)])
      (by positivity)
  have hfirst :
      2 * (7 * k * s * A) * (k₁ / d) * (600 * j * sqrt A / (s * A ^ 5)) ≤
        20160000 * k * K * j / (s * A ^ 9) := by
    calc
      _ ≤ 2 * (7 * k * s * A) * (2400 * K / (s * A ^ 5)) *
          (600 * j / (s * A ^ 5)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc₁ (by positivity)) hu
          (by positivity) (by positivity)
      _ = _ := by field_simp [hs.ne', hA.ne'] <;> ring
  have hsecond :
      (((2 * k * s * A) / (s * A ^ 5 / 100)) * (k₁ / d) +
        (7 * k * s * A) * (k₂ / d ^ 2)) * 2 ≤
        81600000 * k * K * j / (s * A ^ 9) := by
    calc
      _ ≤ (((2 * k * s * A) / (s * A ^ 5 / 100)) * (2400 * K / (s * A ^ 5)) +
          (7 * k * s * A) * (5760000 * K / (s ^ 2 * A ^ 10))) * 2 :=
        mul_le_mul_of_nonneg_right (add_le_add
          (mul_le_mul_of_nonneg_left hc₁ (by positivity))
          (mul_le_mul_of_nonneg_left hc₂ (by positivity))) (by norm_num)
      _ = 81600000 * k * K / (s * A ^ 9) := by
        field_simp [hs.ne', hA.ne'] <;> ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hj
          (by positivity : 0 ≤ 81600000 * k * K / (s * A ^ 9))
        convert h using 1 <;> ring
  have hnum :
      2 * (7 * k * s * A) * (k₁ / d) * (600 * j * sqrt A / (s * A ^ 5)) +
        (((2 * k * s * A) / (s * A ^ 5 / 100)) * (k₁ / d) +
          (7 * k * s * A) * (k₂ / d ^ 2)) * 2 ≤
        101760000 * k * K * j / (s * A ^ 9) := by
    convert add_le_add hfirst hsecond using 1 <;> ring
  have hR : (2 * s) ^ 2 / (12 * (k * (s * A ^ 5 / 100))) ≤ 100 * s / (k * A ^ 5) := by
    calc
      _ = (100 / 3 : ℝ) * (s / (k * A ^ 5)) := by
        field_simp [hs.ne', hk.ne', hA.ne'] <;> ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right
          (by norm_num : (100 / 3 : ℝ) ≤ 100) (by positivity : 0 ≤ s / (k * A ^ 5))
        convert h using 1 <;> ring
  have hmass : (12 * (7 * k * s * A) / a ^ 2) * d ≤ 672 * k * A := by
    have hasq : (s / 2) ^ 2 ≤ a ^ 2 := (sq_le_sq₀ (by positivity) hapos.le).mpr ha
    calc
      _ ≤ (12 * (7 * k * s * A) / (s / 2) ^ 2) * (2 * s) :=
        mul_le_mul (div_le_div_of_nonneg_left (by positivity) (by positivity) hasq)
          hdhi hdpos.le (by positivity)
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hratio : sqrt ((12 * (7 * k * s * A) / a ^ 2) * d) / sqrt lam ≤
      400 / (j * A ^ 2) := by
    rw [← sqrt_div (by positivity : 0 ≤ (12 * (7 * k * s * A) / a ^ 2) * d)]
    apply (sqrt_le_left (by positivity : 0 ≤ 400 / (j * A ^ 2))).mpr
    calc
      _ ≤ (672 * k * A) / lam := div_le_div_of_nonneg_right hmass hlampos.le
      _ ≤ (672 * k * A) / (j ^ 2 * k * A ^ 5 / 200) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlam
      _ = 134400 / (j ^ 2 * A ^ 4) := by
        field_simp [hjpos.ne', hk.ne', hA.ne'] <;> ring
      _ ≤ 160000 / (j ^ 2 * A ^ 4) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ = (400 / (j * A ^ 2)) ^ 2 := by
        field_simp [hjpos.ne', hA.ne'] <;> ring
  calc
    _ = ((2 * s) ^ 2 / (12 * (k * (s * A ^ 5 / 100)))) *
        (2 * (7 * k * s * A) * (k₁ / d) * (600 * j * sqrt A / (s * A ^ 5)) +
          (((2 * k * s * A) / (s * A ^ 5 / 100)) * (k₁ / d) +
            (7 * k * s * A) * (k₂ / d ^ 2)) * 2) *
        (sqrt ((12 * (7 * k * s * A) / a ^ 2) * d) / sqrt lam) := by ring
    _ ≤ (100 * s / (k * A ^ 5)) * (101760000 * k * K * j / (s * A ^ 9)) *
        (400 / (j * A ^ 2)) :=
      mul_le_mul (mul_le_mul hR hnum (by positivity) (by positivity)) hratio
        (by positivity) (by positivity)
    _ = 4070400000000 * K / A ^ 16 := by
      field_simp [hs.ne', hk.ne', hjpos.ne', hA.ne'] <;> ring
    _ ≤ 10000000000000 * (1 + k₁ + k₂) / A ^ 16 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hK) (pow_nonneg hA.le 16)

/-- This universal number contains only the two fixed smooth-cutoff
jet constants; it has no dependence on a cap or a frequency. -/
def terminalMorseSourceBudgetConstant : ℝ :=
  10000000000000 * (1 + terminalPhysicalCutoffJetConstant 1 + terminalPhysicalCutoffJetConstant 2)

theorem terminalMorseSourceBudgetConstant_pos : 0 < terminalMorseSourceBudgetConstant := by
  have h₁ := terminalPhysicalCutoffJetConstant_nonneg 1
  have h₂ := terminalPhysicalCutoffJetConstant_nonneg 2
  unfold terminalMorseSourceBudgetConstant
  positivity

/-- No radius, height, amplitude, or frequency remains in the cost after
the actual boundary normalization. -/
theorem terminalMorseCapSourcePrefactor_normalized (long : Bool)
    {A B j s weightScale lam : ℝ} {r w : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hj : 1 ≤ j) (hs : 0 < s)
    (hscale : 0 < weightScale) (hA₀ : A ≤ 1 / 1000)
    (hr : IsNormalizedMorseCell A B r)
    (hweight : ∀ x ∈ Icc morseCellLeftCut (morseRightCapEnd A B (1 / 100)),
      w (s * r x) = weightScale * (s * deriv r x))
    (hnorm : lam = standInBoundaryScale (j ^ 2)
      (w (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut)))
      (s * r (if long then morseRightCapEnd A B (1 / 100) else morseCellLeftCut))) :
    terminalMorseCapSourcePrefactor long A B j s weightScale lam r ≤
      terminalMorseSourceBudgetConstant / A ^ 16 := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hg := terminalMorseLayer_coarse_geometry long hB hAB hs hA₀ hr
  exact terminalCap_normalized_prefactor_bound hA
    (hA₀.trans (by norm_num : (1 / 1000 : ℝ) ≤ 1)) hj hs hscale
    hg.1 hg.2.1 hg.2.2 (terminalPhysicalCutoffJetConstant_nonneg 1)
    (terminalPhysicalCutoffJetConstant_nonneg 2)
    (terminalMorse_boundary_normalization_lower long hB hAB hs hscale hr hweight hnorm)

end ContinuousFlexibility.Radial

