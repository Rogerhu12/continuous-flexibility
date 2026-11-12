import ContinuousFlexibility.Analysis.MorseOpticalComponentLower
import ContinuousFlexibility.Radial.SeedCentralReturn

/-!
# A fixed optical lower coefficient on the true central component

Only the fixed compact oscillator interval is used to bound the actual
radius speed. The glued seed inherits the estimate from its retained
central germ, rather than from a separately selected reference.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem central_optical_component_lower :
    ∃ κ : ℝ, 0 < κ ∧ ∀ r ∈ Ioo
        (centralRadius (-sqrt centralOscillatorA)) (centralRadius (sqrt centralOscillatorA)),
      κ * min (r - centralRadius (-sqrt centralOscillatorA))
        (centralRadius (sqrt centralOscillatorA) - r) ≤
          -deriv (centralRadialProfile 1) r / (r * centralRadialProfile 1 r) := by
  let s := sqrt centralOscillatorA
  have hs : 0 < s := sqrt_pos.mpr centralOscillatorA_pos
  have hss : s ^ 2 = centralOscillatorA := sq_sqrt centralOscillatorA_pos.le
  have hab : -s < s := by linarith only [hs]
  have hcont : Continuous (deriv centralRadius) :=
    (contDiff_infty_iff_deriv.mp contDiff_centralRadius).2.continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hcont.continuousOn : ContinuousOn (deriv centralRadius) (Icc (-s) s))
  let V := max 1 B
  have hV : 0 < V := zero_lt_one.trans_le (le_max_left _ _)
  have hbound (x : ℝ) (hx : x ∈ Icc (-s) s) : deriv centralRadius x ≤ V :=
    (hB ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  have hmodel (x : ℝ) (hx : x ∈ Icc (-s) s) :
      s * min (x - -s) (s - x) ≤ centralOscillatorA - x ^ 2 := by
    by_cases hx0 : x ≤ 0
    · have he : x - -s ≤ s - x := by linarith only [hx0]
      rw [min_eq_left he]
      have hp := mul_nonneg (neg_nonneg.mpr hx0)
        (show 0 ≤ x + s by linarith only [hx.1])
      nlinarith only [hp, hss]
    · have he : s - x ≤ x - -s := by linarith only [le_of_not_ge hx0]
      rw [min_eq_right he]
      have hp := mul_nonneg (le_of_not_ge hx0) (sub_nonneg.mpr hx.2)
      nlinarith only [hp, hss]
  refine ⟨s / V ^ 3, div_pos hs (pow_pos hV 3), ?_⟩
  intro r hr
  have himage : centralRadius '' Ioo (-s) s =
      Ioo (centralRadius (-s)) (centralRadius s) :=
    contDiff_centralRadius.continuous.image_Ioo_of_strictMono strictMono_centralRadius
  have hrim : r ∈ centralRadius '' Ioo (-s) s := by rw [himage]; exact hr
  obtain ⟨x, hx, rfl⟩ := hrim
  rw [central_opticalDensity_pullback (by norm_num : (0 : ℝ) < 1)]
  exact optical_min_lower_of_radius_pullback hab contDiff_centralRadius hV hs.le
    (fun t _ => deriv_centralRadius_pos t) hbound (Ioo_subset_Icc_self hx)
    (hmodel x (Ioo_subset_Icc_self hx))

theorem SeedGluedPair.central_optical_component_lower
    {D : ReferenceData} {c d : ℝ} {uL uR : ℝ → ℝ}
    {K : SeedCentralCutoff} {q : ℝ}
    (G : SeedGluedPair D c d uL uR K q) (hq : 0 < q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ r ∈ Ioo
        (centralRadius (-sqrt centralOscillatorA)) (centralRadius (sqrt centralOscillatorA)),
      κ * min (r - centralRadius (-sqrt centralOscillatorA))
        (centralRadius (sqrt centralOscillatorA) - r) ≤
          -deriv G.profile r / (r * G.profile r) := by
  obtain ⟨κ, hκ, hbound⟩ := central_optical_component_lower
  refine ⟨κ, hκ, ?_⟩
  intro r hr
  have hg := G.central_profile_germ hq (Ioo_subset_Icc_self hr)
  rw [hg.deriv_eq, hg.eq_of_nhds]
  exact hbound r hr

end ContinuousFlexibility.Radial
