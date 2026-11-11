import ContinuousFlexibility.Radial.ModeLocalMeasure
import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# A uniform total mass bound from the actual profile estimates

The zeroth cell estimate bounds the entire profile, because the partition
covers every interior point.  Its stretched exponential has a fixed
maximum controlled by the same profile constant.  Thus every outer
restriction has a mass bound independent of its cut and frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

/-- The actual partition covers the physical open interval. -/
theorem outer_profile_cell_cover {D : ReferenceData} (hpart : RadialPartition D)
    {r : ℝ} (hr : r ∈ radialCore D) : ∃ m, r ∈ D.cells m := by
  by_contra h
  have hz (m : ℕ) : D.localizer m r = 0 := by
    apply Function.notMem_support.mp
    intro hm
    exact h ⟨m, hpart.2.2.1 m hm⟩
  have hsum := (hpart.2.2.2.2.1 r hr).2
  have hzero : (0 : ℝ) = 1 := by simpa only [hz, tsum_zero] using hsum
  exact zero_ne_one hzero

/-- The coefficient in the profile's zeroth estimate is uniformly bounded. -/
theorem outer_profile_exponent_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    -t ^ (5 / 2 : ℝ) + c * t ^ 2 ≤ c ^ 5 := by
  rw [ssv_rpow_five_half ht]
  by_cases hs : c ≤ sqrt t
  · calc
      -(t ^ 2 * sqrt t) + c * t ^ 2 = (c - sqrt t) * t ^ 2 := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sq_nonneg _)
      _ ≤ c ^ 5 := pow_nonneg hc _
  · have htC : t ≤ c ^ 2 := by
      have hsq := pow_le_pow_left₀ (sqrt_nonneg t) (le_of_not_ge hs) 2
      rwa [sq_sqrt ht] at hsq
    have ht2 : t ^ 2 ≤ c ^ 4 := by
      have hsq := pow_le_pow_left₀ ht htC 2
      simpa only [← pow_mul] using hsq
    calc
      -(t ^ 2 * sqrt t) + c * t ^ 2 ≤ c * t ^ 2 := by
        linarith [mul_nonneg (sq_nonneg t) (sqrt_nonneg t)]
      _ ≤ c * c ^ 4 := mul_le_mul_of_nonneg_left ht2 hc
      _ = c ^ 5 := by ring

/-- One common cell constant gives a common global profile height bound. -/
theorem outer_profile_height_le {D : ReferenceData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) {r : ℝ} (hr : r ∈ radialCore D) :
    D.w r ≤ C 0 * exp ((C 0) ^ 5) := by
  rcases hC with ⟨_, hpart, hCpos, _, _, _, _, _, hjet, _, _, _, _⟩
  obtain ⟨m, hm⟩ := outer_profile_cell_cover hpart hr
  have hcell : |D.w r| ≤ C 0 *
      exp (-(D.cellIndex m : ℝ) ^ (5 / 2 : ℝ) + C 0 * (D.cellIndex m : ℝ) ^ 2) := by
    simpa only [radialJet] using hjet m r hm 0
  exact (le_abs_self _).trans (hcell.trans
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (outer_profile_exponent_le (Nat.cast_nonneg _) (hCpos 0).le)) (hCpos 0).le))

/-- The actual Hilbert mass has a bound depending only on the common
profile constant and the two physical endpoints. -/
theorem outer_radialHilbertMeasure_mass_bound {D : ReferenceData} {C : ℕ → ℝ}
    (hC : AccumulatingProfileBounds D C) :
    (radialHilbertMeasure D).real univ ≤
      12 * C 0 * exp ((C 0) ^ 5) * (D.b - D.a) / D.a ^ 2 := by
  have hD : IsAccumulatingProfile D := ⟨C, hC⟩
  have ha : 0 < D.a := hC.1.1
  have hab : D.a ≤ D.b := hC.1.2.1.le
  have hc : 0 < C 0 := hC.2.2.1 0
  have hρ : ∀ r ∈ Ioo D.a D.b,
      matchingDensity D r ≤ 12 * C 0 * exp ((C 0) ^ 5) / D.a ^ 2 := by
    intro r hr
    have hrpos : 0 < r := ha.trans hr.1
    have hw := outer_profile_height_le hC hr
    have hnum : 12 * D.w r ≤ 12 * C 0 * exp ((C 0) ^ 5) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 12)
    have hden : D.a ^ 2 ≤ r ^ 2 := (sq_le_sq₀ ha.le hrpos.le).mpr hr.1.le
    unfold matchingDensity
    apply (div_le_div_iff₀ (pow_pos hrpos 2) (pow_pos ha 2)).mpr
    exact (mul_le_mul_of_nonneg_right hnum (sq_nonneg D.a)).trans
      (mul_le_mul_of_nonneg_left hden (by positivity))
  calc
    (radialHilbertMeasure D).real univ = ∫ r in D.a..D.b, matchingDensity D r := by
      simpa only [integral_const, smul_eq_mul, mul_one] using
        matchingDensity_integral hD (fun _ => (1 : ℝ))
    _ ≤ ∫ _r in D.a..D.b, 12 * C 0 * exp ((C 0) ^ 5) / D.a ^ 2 :=
      intervalIntegral.integral_mono_on_of_le_Ioo hab
        ((matchingDensity_continuousOn hD).intervalIntegrable_of_Icc hab)
        intervalIntegrable_const hρ
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring

end ContinuousFlexibility.Radial
