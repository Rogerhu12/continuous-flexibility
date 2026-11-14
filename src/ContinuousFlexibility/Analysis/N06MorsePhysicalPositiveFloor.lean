module

public import ContinuousFlexibility.Analysis.N06MorsePositiveFloor
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Physical distance lower bounds on the actual positive Morse caps

The model estimate is transported using the literal profile identity
`w (R x) = amplitude * R' x` and the real mean value theorem for `R`.
One constant works for both physical tails, both exterior caps, and all
retained indices. The estimate covers the whole cap, including the part
away from its root, rather than relying on compactness separately on each
model interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A single coefficient-power constant bounds the true physical
coefficient below by the physical distance to the adjoining root, on both
whole positive model caps. The model realization is the only geometric
premise. -/
theorem n06_morseRealization_positive_cap_distance_lower
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (side : Bool) (n : ℕ), T.index ≤ n →
      ∀ (right : Bool) (t : ℝ), 0 ≤ t →
      let x := n06MorseOuterPoint (morseChainA T n) (morseChainB T n) right t
      let x₀ := n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right
      x ∈ Icc (T.leftX side n) (T.rightX side n) →
        c * radialE n ^ (-12 : ℝ) * |T.radius side n x - T.radius side n x₀| ≤
          deriv D.w (T.radius side n x) / T.radius side n x := by
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuous.continuousOn : ContinuousOn D.w (Icc D.a D.b))
  let M : ℝ := max M₀ (max 2 (D.b - D.a))
  have h2M : 2 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h1M : 1 ≤ M := (by norm_num : (1 : ℝ) ≤ 2).trans h2M
  have hM : 0 < M := zero_lt_one.trans_le h1M
  have hspan : D.b - D.a ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hwM (r : ℝ) (hr : r ∈ Icc D.a D.b) : |D.w r| ≤ M := by
    have hb : |D.w r| ≤ M₀ := by simpa only [Real.norm_eq_abs] using hM₀ r hr
    exact hb.trans (le_max_left _ _)
  let c : ℝ := ((3 : ℝ) ^ 9)⁻¹ / (4 * M ^ 3)
  refine ⟨c, div_pos (inv_pos.mpr (by norm_num))
    (mul_pos (by norm_num) (pow_pos hM 3)), ?_⟩
  intro side n hn right t ht
  let x : ℝ := n06MorseOuterPoint (morseChainA T n) (morseChainB T n) right t
  let x₀ : ℝ := n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right
  change x ∈ Icc (T.leftX side n) (T.rightX side n) → _
  intro hx
  let R : ℝ → ℝ := T.radius side n
  let amplitude : ℝ := morseChainAmplitude T σ n
  let B : ℝ := morseChainB T n
  let ρ : ℝ → ℝ := morseRho (morseChainA T n) B
  let d : ℝ := |R x - R x₀|
  have hd : 0 ≤ d := abs_nonneg _
  have hp := hreal.retained_data side n hn
  have hB : 0 < B := hp.1
  have hroot : ρ x₀ = 0 := n06_morseOuterRoot_zero hp.1 hp.2.1 right
  have hx₀i := n06_morseRealization_root_mem_Ioo hreal side hn hroot
  have hx₀ : x₀ ∈ Icc (T.leftX side n) (T.rightX side n) := ⟨hx₀i.1.le, hx₀i.2.le⟩
  have hr := hreal.radius_mem_core side n hn x hx
  have hr₀ := hreal.radius_mem_core side n hn x₀ hx₀
  have hrp : 0 < R x := hreal.geometry.1.trans hr.1
  have hwp : 0 < D.w (R x) := hreal.geometry.2.2.2.2.1 (R x) hr
  have hamp : 0 < amplitude := morseChainAmplitude_pos T σ hσ n
  have hampM : amplitude ≤ M := (n06_morseChainAmplitude_le_two T σ hσ n).trans h2M
  have hdM : d ≤ M := by
    have hb : |R x - R x₀| ≤ D.b - D.a := abs_le.mpr
      ⟨by linarith only [hr.1, hr₀.2], by linarith only [hr.2, hr₀.1]⟩
    exact hb.trans hspan
  have hR : ContDiff ℝ ∞ R := hreal.radius_smooth side n hn
  have hspeed (u : ℝ) (hu : u ∈ Icc (T.leftX side n) (T.rightX side n)) :
      ‖deriv R u‖ ≤ M / amplitude := by
    have hv : 0 < deriv R u := hreal.derivative_positive side n hn u hu
    rw [Real.norm_eq_abs, abs_of_pos hv]
    apply (le_div_iff₀ hamp).mpr
    have hpr : D.w (R u) = amplitude * deriv R u := hreal.profile_eq side n hn u hu
    have hru := hreal.radius_mem_core side n hn u hu
    calc
      deriv R u * amplitude = D.w (R u) := by rw [hpr]; ring
      _ ≤ |D.w (R u)| := le_abs_self _
      _ ≤ M := hwM (R u) ⟨hru.1.le, hru.2.le⟩
  have hdist : |x - x₀| = t := n06_morseOuterPoint_distance _ _ right ht
  have hLip : d ≤ (M / amplitude) * t := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u _ => hR.differentiable (by simp) u) hspeed
      (convex_Icc (T.leftX side n) (T.rightX side n)) hx₀ hx
    have hh' : |R x - R x₀| ≤ (M / amplitude) * |x - x₀| := by
      simpa only [Real.norm_eq_abs] using hh
    rwa [hdist] at hh'
  have hLipMul : amplitude * d ≤ M * t := by
    calc
      amplitude * d ≤ amplitude * ((M / amplitude) * t) :=
        mul_le_mul_of_nonneg_left hLip hamp.le
      _ = M * t := by field_simp [hamp.ne'] <;> ring
  have hM2 : M ≤ M ^ 2 := by nlinarith only [h1M]
  have hmin : amplitude * d / M ^ 2 ≤ min t 1 := by
    apply le_min
    · apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
      exact hLipMul.trans (by simpa only [mul_comm t] using
        mul_le_mul_of_nonneg_right hM2 ht)
    · apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
      have hh := mul_le_mul hampM hdM hd hM.le
      simpa only [one_mul, pow_two] using hh
  have hd2 : (2 : ℝ) ≤ T.d n := by
    rw [hreal.d_eq n hn]
    exact_mod_cast morseChainInteger_ge_two n
  have hmodel : B / 4 * min t 1 ≤ -ρ x :=
    n06_morseRho_positive_cap_distance_lower hB
      (n06_morseChain_eight_mul_B_le_A T n hd2) right ht
  have hρ : 0 ≤ -ρ x :=
    (mul_nonneg (div_nonneg hB.le (by norm_num)) (le_min ht zero_le_one)).trans hmodel
  have hfloor : B / 4 * (amplitude * d / M ^ 2) ≤ -ρ x :=
    (mul_le_mul_of_nonneg_left hmin (div_nonneg hB.le (by norm_num))).trans hmodel
  have hprofile : D.w (R x) = amplitude * deriv R x := hreal.profile_eq side n hn x hx
  have hscaled : deriv D.w (R x) * deriv R x = amplitude * (-ρ x * R x) :=
    morseRealization_profile_deriv_scaled hreal side hn hx
  have hidentity : (deriv D.w (R x) / R x) * D.w (R x) = amplitude ^ 2 * (-ρ x) := by
    calc
      _ = (amplitude / R x) * (deriv D.w (R x) * deriv R x) := by
        rw [hprofile]
        ring
      _ = (amplitude / R x) * (amplitude * (-ρ x * R x)) := by rw [hscaled]
      _ = amplitude ^ 2 * (-ρ x) := by field_simp [hrp.ne'] <;> ring
  have hfield : deriv D.w (R x) / R x = amplitude ^ 2 * (-ρ x) / D.w (R x) :=
    (eq_div_iff hwp.ne').mpr hidentity
  have hraw : (amplitude ^ 3 * B / (4 * M ^ 3)) * d ≤ deriv D.w (R x) / R x := by
    calc
      _ = (amplitude ^ 2 / M) * (B / 4 * (amplitude * d / M ^ 2)) := by
        field_simp [hM.ne'] <;> ring
      _ ≤ (amplitude ^ 2 / M) * (-ρ x) :=
        mul_le_mul_of_nonneg_left hfloor (div_nonneg (sq_nonneg _) hM.le)
      _ = (amplitude ^ 2 * (-ρ x)) / M := by ring
      _ ≤ (amplitude ^ 2 * (-ρ x)) / D.w (R x) :=
        div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hρ) hwp
          ((le_abs_self _).trans (hwM (R x) ⟨hr.1.le, hr.2.le⟩))
      _ = deriv D.w (R x) / R x := hfield.symm
  change c * radialE n ^ (-12 : ℝ) * d ≤ deriv D.w (R x) / R x
  calc
    c * radialE n ^ (-12 : ℝ) * d =
        (((3 : ℝ) ^ 9)⁻¹ * radialE n ^ (-12 : ℝ)) / (4 * M ^ 3) * d := by
      dsimp only [c]
      ring
    _ ≤ (amplitude ^ 3 * B) / (4 * M ^ 3) * d :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (n06_morseChain_amplitude_cubic_lower T σ hσ n (hreal.d_eq n hn))
          (mul_nonneg (by norm_num) (pow_nonneg hM.le 3))) hd
    _ ≤ deriv D.w (R x) / R x := hraw

end ContinuousFlexibility.Analysis
