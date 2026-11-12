import ContinuousFlexibility.Analysis.N06MorsePositiveComponent
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A quantitative width for the actual positive Morse gaps

The original reciprocal profile bound controls the physical speed of
every retained model from below. The fixed short left cap therefore has
a physical width bounded below by a coefficient power. Each positive
gap contains one such actual cap, on either physical tail.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The true physical radius speed has a lower bound throughout every
retained model, obtained from its original profile identity. -/
theorem n06_morseRealization_radius_deriv_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) {x : ℝ}
    (hx : x ∈ Icc (T.leftX side n) (T.rightX side n)) :
    (1 / (2 * C 0)) * radialE n ^ (-C 0) ≤ deriv (T.radius side n) x := by
  have hr := hreal.radius_mem_core side n hn x hx
  have hwp : 0 < D.w (T.radius side n x) := hreal.geometry.2.2.2.2.1 _ hr
  have hCp : 0 < C 0 := hreal.constants_pos 0
  have hamp : 0 < morseChainAmplitude T σ n := morseChainAmplitude_pos T σ hσ n
  have hampU : morseChainAmplitude T σ n ≤ 2 := n06_morseChainAmplitude_le_two T σ hσ n
  obtain ⟨m, hm, hrm⟩ := hreal.2.2.2.2.2.2.2.2.1 side n hn _
    (morseRealization_model_subset_block hreal side hn ⟨x, hx, rfl⟩)
  have hprofile : (C 0)⁻¹ * radialE n ^ (-C 0) ≤ D.w (T.radius side n x) := by
    simpa only [hm] using n06_accumulatingProfile_cell_lower hreal.accumulating m hrm
  have hidentity := hreal.profile_eq side n hn x hx
  calc
    (1 / (2 * C 0)) * radialE n ^ (-C 0) =
        ((C 0)⁻¹ * radialE n ^ (-C 0)) / 2 := by field_simp [hCp.ne']
    _ ≤ D.w (T.radius side n x) / 2 := div_le_div_of_nonneg_right hprofile (by norm_num)
    _ ≤ D.w (T.radius side n x) / morseChainAmplitude T σ n :=
      div_le_div_of_nonneg_left hwp.le hamp hampU
    _ = deriv (T.radius side n) x := by rw [hidentity, mul_div_cancel_left₀ _ hamp.ne']

/-- Integrating that same pointwise speed bound gives actual radius
separation between any two retained model points. -/
theorem n06_morseRealization_radius_growth_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) {x y : ℝ}
    (hx : x ∈ Icc (T.leftX side n) (T.rightX side n))
    (hy : y ∈ Icc (T.leftX side n) (T.rightX side n)) (hxy : x ≤ y) :
    ((1 / (2 * C 0)) * radialE n ^ (-C 0)) * (y - x) ≤
      T.radius side n y - T.radius side n x := by
  have hR := hreal.radius_smooth side n hn
  exact (convex_Icc (T.leftX side n) (T.rightX side n)).mul_sub_le_image_sub_of_le_deriv
    hR.continuous.continuousOn (hR.differentiable (by simp)).differentiableOn
    (fun t ht => n06_morseRealization_radius_deriv_lower hreal hσ side hn (interior_subset ht))
    x hx y hy hxy

/-- The fixed original short cap forces a true physical lower width
for every full left cap. -/
theorem n06_morseRealization_left_cap_width_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) :
    (morseShortLeftCapLength / (2 * C 0)) * radialE n ^ (-C 0) ≤
      T.radius side n (morseLeftTurn (morseChainA T n) (morseChainB T n)) -
        T.radius side n (T.leftX side n) := by
  have hp := hreal.retained_data side n hn
  obtain ⟨hl, hlr, hr⟩ := morseRealization_turns_retained hreal side hn
  have hleft : T.leftX side n ∈ Icc (T.leftX side n) (T.rightX side n) :=
    ⟨le_rfl, (hl.trans (hlr.trans hr)).le⟩
  have hroot : morseLeftTurn (morseChainA T n) (morseChainB T n) ∈
      Icc (T.leftX side n) (T.rightX side n) := ⟨hl.le, (hlr.trans hr).le⟩
  have hlen : morseShortLeftCapLength ≤
      morseLeftTurn (morseChainA T n) (morseChainB T n) - T.leftX side n := by
    rw [hp.2.2.1]
    change morseShortLeftCapCut - morseCellLeftCut ≤
      morseLeftTurn (morseChainA T n) (morseChainB T n) - morseCellLeftCut
    exact sub_le_sub_right (morseShortLeftCapCut_lt_leftTurn hp.1 hp.2.1).le _
  have hspeed : 0 ≤ (1 / (2 * C 0)) * radialE n ^ (-C 0) :=
    mul_nonneg (one_div_nonneg.mpr (mul_nonneg (by norm_num) (hreal.constants_pos 0).le))
      (Real.rpow_nonneg (exp_pos _).le _)
  calc
    (morseShortLeftCapLength / (2 * C 0)) * radialE n ^ (-C 0) =
        ((1 / (2 * C 0)) * radialE n ^ (-C 0)) * morseShortLeftCapLength := by ring
    _ ≤ ((1 / (2 * C 0)) * radialE n ^ (-C 0)) *
        (morseLeftTurn (morseChainA T n) (morseChainB T n) - T.leftX side n) :=
      mul_le_mul_of_nonneg_left hlen hspeed
    _ ≤ _ := n06_morseRealization_radius_growth_lower hreal hσ side hn hleft hroot hl.le

/-- Every actual positive gap contains an arrival left cap. Its length
therefore has a fixed coefficient-power lower bound as well. -/
theorem n06_morseRealization_positive_gap_length_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) :
    (morseShortLeftCapLength / (2 * C 0)) * radialE (n + 1) ^ (-C 0) ≤
      n06MorsePositiveRight T side n - n06MorsePositiveLeft T side n := by
  let a : ℕ := if side then n + 1 else n
  have ha : T.index ≤ a := by
    cases side
    · exact hn
    · exact hn.trans (Nat.le_succ n)
  have haN : a ≤ n + 1 := by
    cases side
    · exact Nat.le_succ n
    · exact le_rfl
  have hj := hreal.join_data side n hn
  have hjR : T.joinRight side n = T.radius side a (T.leftX side a) := by
    cases side <;> exact hj.2.2.1
  have hbound : (morseShortLeftCapLength / (2 * C 0)) * radialE a ^ (-C 0) ≤
      n06MorsePositiveRight T side n - T.joinRight side n := by
    rw [hjR]
    exact n06_morseRealization_left_cap_width_lower hreal hσ side ha
  have hmono : radialE (n + 1) ^ (-C 0) ≤ radialE a ^ (-C 0) :=
    Real.rpow_le_rpow_of_nonpos (exp_pos _)
      (exp_le_exp.mpr (radialQ_monotone haN)) (neg_nonpos.mpr (hreal.constants_pos 0).le)
  have hgeom := n06_morsePositive_gap_geometry hreal side hn
  calc
    (morseShortLeftCapLength / (2 * C 0)) * radialE (n + 1) ^ (-C 0) ≤
        (morseShortLeftCapLength / (2 * C 0)) * radialE a ^ (-C 0) :=
      mul_le_mul_of_nonneg_left hmono (div_nonneg morseShortLeftCapLength_pos.le
        (mul_nonneg (by norm_num) (hreal.constants_pos 0).le))
    _ ≤ n06MorsePositiveRight T side n - T.joinRight side n := hbound
    _ ≤ n06MorsePositiveRight T side n - n06MorsePositiveLeft T side n :=
      sub_le_sub_left (hgeom.2.1.trans hgeom.2.2.1).le _

end ContinuousFlexibility.Analysis
