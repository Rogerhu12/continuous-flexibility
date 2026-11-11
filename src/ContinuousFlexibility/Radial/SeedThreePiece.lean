import ContinuousFlexibility.Radial.SeedPairGluing

/-! # Three-piece gluing with complete germs at both cuts -/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff

def seedThreeGlue (l h : ℝ) (fL fM fR : ℝ → ℝ) : ℝ → ℝ :=
  morseGlueCut l fL (morseGlueCut h fM fR)

theorem seedThreeGlue_left_match {l h : ℝ} {fL fM fR : ℝ → ℝ}
    (hlh : l < h) (hL : fL =ᶠ[𝓝 l] fM) (hR : fM =ᶠ[𝓝 h] fR) :
    fL =ᶠ[𝓝 l] morseGlueCut h fM fR :=
  hL.trans (morseGlueCut_eventually_left hR hlh.le).symm

theorem seedThreeGlue_left_germ {l h r : ℝ} {fL fM fR : ℝ → ℝ}
    (hlh : l < h) (hL : fL =ᶠ[𝓝 l] fM) (hR : fM =ᶠ[𝓝 h] fR)
    (hr : r ≤ l) : seedThreeGlue l h fL fM fR =ᶠ[𝓝 r] fL :=
  morseGlueCut_eventually_left (seedThreeGlue_left_match hlh hL hR) hr

theorem seedThreeGlue_middle_germ {l h r : ℝ} {fL fM fR : ℝ → ℝ}
    (hlh : l < h) (hL : fL =ᶠ[𝓝 l] fM) (hR : fM =ᶠ[𝓝 h] fR)
    (hr : r ∈ Icc l h) : seedThreeGlue l h fL fM fR =ᶠ[𝓝 r] fM :=
  (morseGlueCut_eventually_right (seedThreeGlue_left_match hlh hL hR) hr.1).trans
    (morseGlueCut_eventually_left hR hr.2)

theorem seedThreeGlue_right_germ {l h r : ℝ} {fL fM fR : ℝ → ℝ}
    (hlh : l < h) (hL : fL =ᶠ[𝓝 l] fM) (hR : fM =ᶠ[𝓝 h] fR)
    (hr : h ≤ r) : seedThreeGlue l h fL fM fR =ᶠ[𝓝 r] fR :=
  (morseGlueCut_eventually_right (seedThreeGlue_left_match hlh hL hR)
    (hlh.le.trans hr)).trans (morseGlueCut_eventually_right hR hr)

theorem contDiffOn_seedThreeGlue {l h : ℝ} {fL fM fR : ℝ → ℝ}
    (hlh : l < h) (hL : fL =ᶠ[𝓝 l] fM) (hR : fM =ᶠ[𝓝 h] fR)
    (hsL : ContDiffOn ℝ ∞ fL (Ioi 0))
    (hsM : ContDiffOn ℝ ∞ fM (Ioi 0))
    (hsR : ContDiffOn ℝ ∞ fR (Ioi 0)) :
    ContDiffOn ℝ ∞ (seedThreeGlue l h fL fM fR) (Ioi 0) :=
  contDiffOn_morseGlueCut_positive hsL
    (contDiffOn_morseGlueCut_positive hsM hsR hR) (seedThreeGlue_left_match hlh hL hR)

theorem seedRescale_simple_critical {R A r : ℝ} {f : ℝ → ℝ}
    (hR : R ≠ 0) (hA : A ≠ 0)
    (hsimple : deriv f (R⁻¹ * r) = 0 → deriv (deriv f) (R⁻¹ * r) ≠ 0)
    (hzero : deriv (seedRescale R A f) r = 0) :
    deriv (deriv (seedRescale R A f)) r ≠ 0 := by
  rw [deriv_seedRescale] at hzero
  have hc : A * R⁻¹ ≠ 0 := mul_ne_zero hA (inv_ne_zero hR)
  have hd : deriv f (R⁻¹ * r) = 0 := (mul_eq_zero.mp hzero).resolve_left hc
  rw [deriv_seedRescale]
  change deriv (seedRescale R (A * R⁻¹) (deriv f)) r ≠ 0
  rw [deriv_seedRescale]
  exact mul_ne_zero (mul_ne_zero hc (inv_ne_zero hR)) (hsimple hd)

theorem seedRescale_deriv_pos {R A r : ℝ} {f : ℝ → ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : 0 < deriv f (R⁻¹ * r)) :
    0 < deriv (seedRescale R A f) r := by
  rw [deriv_seedRescale]
  exact mul_pos (mul_pos hA (inv_pos.mpr hR)) hf

theorem seedRescale_match_cone {R c a c₀ a₀ p r : ℝ} {w u : ℝ → ℝ}
    (hR : 0 < R) (hr : 0 < r) (hc : c₀ ≠ 0) (ha : a₀ ≠ 0)
    (hw : w (R⁻¹ * r) = c₀ * (R⁻¹ * r))
    (hu : u (R⁻¹ * r) = a₀ * (R⁻¹ * r) ^ p) :
    seedRescale R ((c / c₀) * R) w r = c * r ∧
      seedRescale R (a * R ^ p / a₀) u r = a * r ^ p := by
  constructor
  · rw [seedRescale_cone hR.ne' hw]
    field_simp [hc]
  · rw [seedRescale_power hR hr hu]
    have hp : R ^ p ≠ 0 := (rpow_pos_of_pos hR p).ne'
    field_simp [ha, hp]
    <;> ring

end ContinuousFlexibility.Radial
