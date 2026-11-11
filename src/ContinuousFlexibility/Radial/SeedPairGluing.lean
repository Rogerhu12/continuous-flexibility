import ContinuousFlexibility.Radial.ReferenceCoordinate
import ContinuousFlexibility.Radial.MorseChainLocalGluing

/-!
# Local gluing and exact rescaling of radial seed pairs
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem radialJacobi_eq_of_germs {w W u U : ℝ → ℝ} {a r : ℝ}
    (hw : W =ᶠ[𝓝 r] w) (hu : U =ᶠ[𝓝 r] u) :
    radialJacobi a W U r = radialJacobi a w u r := by
  have hflux : (fun x => W x * deriv U x) =ᶠ[𝓝 r] fun x => w x * deriv u x := by
    filter_upwards [hw, hu.deriv] with x hx hdx
    rw [hx, hdx]
  unfold radialJacobi
  rw [hflux.deriv_eq, hw.deriv_eq, hu.eq_of_nhds]

theorem contDiffOn_morseGlueCut_positive {c : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (hfg : f =ᶠ[𝓝 c] g) :
    ContDiffOn ℝ ∞ (morseGlueCut c f g) (Ioi 0) := by
  intro r hr
  rcases le_total r c with h | h
  · exact ((hf.contDiffAt (Ioi_mem_nhds hr)).congr_of_eventuallyEq
      (morseGlueCut_eventually_left hfg h)).contDiffWithinAt
  · exact ((hg.contDiffAt (Ioi_mem_nhds hr)).congr_of_eventuallyEq
      (morseGlueCut_eventually_right hfg h)).contDiffWithinAt

def seedRescale (R A : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  A * f (R⁻¹ * r)

theorem deriv_seedRescale (R A : ℝ) (f : ℝ → ℝ) :
    deriv (seedRescale R A f) =
      fun r => A * R⁻¹ * deriv f (R⁻¹ * r) := by
  funext r
  unfold seedRescale
  rw [deriv_const_mul_field, deriv_scalar_coordinate]
  ring

theorem seedRescale_at_scaled {R : ℝ} (hR : R ≠ 0) (A : ℝ)
    (f : ℝ → ℝ) (r : ℝ) :
    seedRescale R A f (R * r) = A * f r := by
  simp only [seedRescale, inv_mul_cancel_left₀ hR]

theorem contDiffOn_seedRescale {R A : ℝ} {f : ℝ → ℝ}
    (hR : 0 < R) (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (seedRescale R A f) (Ioi 0) := by
  exact contDiffOn_const.mul
    (hf.comp (contDiff_const.mul contDiff_id).contDiffOn
      (fun r hr => mul_pos (inv_pos.mpr hR) hr))

theorem radialJacobi_seedRescale {R H A a r : ℝ} {w u : ℝ → ℝ}
    (hR : R ≠ 0) (hr : r ≠ 0) :
    radialJacobi a (seedRescale R (H * R) w) (seedRescale R A u) (R * r) =
      (H * A / R) * radialJacobi a w u r := by
  have hflux : (fun x => seedRescale R (H * R) w x *
      deriv (seedRescale R A u) x) =
      seedRescale R (H * A) (fun x => w x * deriv u x) := by
    funext x
    rw [deriv_seedRescale]
    dsimp only [seedRescale]
    field_simp [hR]
    <;> ring
  unfold radialJacobi
  rw [hflux, deriv_seedRescale, deriv_seedRescale]
  simp only [seedRescale, inv_mul_cancel_left₀ hR]
  field_simp [hR, hr]
  <;> ring

theorem seedRescale_cone {R H c r : ℝ} {w : ℝ → ℝ}
    (hR : R ≠ 0) (hw : w (R⁻¹ * r) = c * (R⁻¹ * r)) :
    seedRescale R (H * R) w r = (H * c) * r := by
  rw [seedRescale, hw]
  field_simp [hR]
  <;> ring

theorem seedRescale_power {R A c p r : ℝ} {u : ℝ → ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hu : u (R⁻¹ * r) = c * (R⁻¹ * r) ^ p) :
    seedRescale R A u r = (A * c / R ^ p) * r ^ p := by
  rw [seedRescale, hu, mul_rpow (inv_nonneg.mpr hR.le) hr.le,
    inv_rpow hR.le]
  ring

def seedZeroBelow (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  if 0 < r then f r else 0

theorem seedZeroBelow_germ {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r) :
    seedZeroBelow f =ᶠ[𝓝 r] f := by
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact if_pos hx

theorem contDiff_seedZeroBelow {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : ContDiffOn ℝ ∞ f (Ioi 0))
    (hzero : ∀ r, 0 < r → r < a → f r = 0) :
    ContDiff ℝ ∞ (seedZeroBelow f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : 0 < r
  · exact (hf.contDiffAt (Ioi_mem_nhds hr)).congr_of_eventuallyEq (seedZeroBelow_germ hr)
  · have hle : r ≤ 0 := le_of_not_gt hr
    have hg : seedZeroBelow f =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (hle.trans_lt ha)] with x hx
      by_cases hp : 0 < x
      · rw [seedZeroBelow, if_pos hp, hzero x hp hx]
      · rw [seedZeroBelow, if_neg hp]
    exact contDiffAt_const.congr_of_eventuallyEq hg

end ContinuousFlexibility.Radial
