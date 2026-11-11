import ContinuousFlexibility.Radial.R11bWeightedBessel

/-!
# Actual weighted squares of individual angular modes

These quantities are the original localized radial square integrals with
the output weights. A.e. proportionality of the coefficient functions
scales the whole square series by the scalar squared.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

def r11bWeightedModeSquare (D : ReferenceData) (γ M : ℝ)
    (f : PolarPoint → ℝ) (j : ℕ) : ℝ :=
  ∑' m, exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    ∫ r, (D.localizer m r * referenceMode f j r) ^ 2 ∂volume.restrict (radialCore D)

theorem r11bWeightedModeSquare_nonneg (D : ReferenceData) (γ M : ℝ)
    (f : PolarPoint → ℝ) (j : ℕ) : 0 ≤ r11bWeightedModeSquare D γ M f j :=
  tsum_nonneg fun m => mul_nonneg (exp_pos _).le (integral_nonneg fun r => sq_nonneg _)

theorem r11b_weightedModeSquare_scale_ae (D : ReferenceData) (γ M : ℝ)
    {f g : PolarPoint → ℝ} {j : ℕ} {c : ℝ}
    (h : referenceMode f j =ᵐ[volume.restrict (radialCore D)]
      (fun r => c * referenceMode g j r)) :
    r11bWeightedModeSquare D γ M f j = c ^ 2 * r11bWeightedModeSquare D γ M g j := by
  have hi (m : ℕ) :
      (∫ r, (D.localizer m r * referenceMode f j r) ^ 2
        ∂volume.restrict (radialCore D)) =
      c ^ 2 * ∫ r, (D.localizer m r * referenceMode g j r) ^ 2
        ∂volume.restrict (radialCore D) := by
    calc
      _ = ∫ r, c ^ 2 * (D.localizer m r * referenceMode g j r) ^ 2
          ∂volume.restrict (radialCore D) := by
        apply integral_congr_ae
        filter_upwards [h] with r hr
        change referenceMode f j r = c * referenceMode g j r at hr
        change (D.localizer m r * referenceMode f j r) ^ 2 =
          c ^ 2 * (D.localizer m r * referenceMode g j r) ^ 2
        rw [hr]
        ring
      _ = _ := integral_const_mul _ _
  unfold r11bWeightedModeSquare
  calc
    _ = ∑' m, c ^ 2 *
        (exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          ∫ r, (D.localizer m r * referenceMode g j r) ^ 2
            ∂volume.restrict (radialCore D)) := by
      apply tsum_congr
      intro m
      rw [hi m]
      ring
    _ = _ := tsum_mul_left

theorem r11b_output_even_mode_squares {D : ReferenceData} (hab : D.a ≤ D.b)
    (J : Finset ℕ) (hJ : ∀ n ∈ J, 0 < n)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U) :
    (∑ n ∈ J, r11bWeightedModeSquare D γ M (outputRemainder D a U) (2 * n)) ≤
      outputNormSquare D γ M a U := by
  have hfreq (i j : ℕ) : (2 * i = 2 * j) ↔ i = j := by omega
  have horth : ∀ i ∈ J, ∀ j ∈ J,
      angularPairing (cosineMode (2 * i)) (cosineMode (2 * j)) =
        if i = j then 1 else 0 := by
    intro i hi j hj
    simpa only [hfreq] using angularPairing_cosineMode (2 * i) (2 * j)
      (Nat.mul_pos (by decide) (hJ i hi)) (Nat.mul_pos (by decide) (hJ j hj))
  have hb := (r11b_output_weighted_finite_bessel hab J (fun n => cosineMode (2 * n)) hU
    (fun n _ => cosineMode_memLp_angularInterval (2 * n)) horth).2
  simpa only [r11bWeightedModeSquare, referenceMode, radialAngularMean,
    angularPairing, angularAverage, one_div] using hb

end ContinuousFlexibility.Radial
