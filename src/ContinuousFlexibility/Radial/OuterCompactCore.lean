module

public import ContinuousFlexibility.Radial.OuterFullCoreTransfer
public import ContinuousFlexibility.Radial.OuterFullCoreMass

/-!
# Uniform finite-frequency estimates on a fixed regular compact interval

This is the finite initial-cell input.  The constants are actual
coefficient integrals on a fixed compact subset of the annulus, and
are independent of the solution and of the frequency in the finite band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

theorem outer_signed_state_energy_transfer {u z α β : ℝ → ℝ} {l r s t : ℝ}
    (hlr : l ≤ r) (hα : ContinuousOn α (Icc l r)) (hβ : ContinuousOn β (Icc l r))
    (hd : ∀ x ∈ Icc l r,
      HasDerivAt u (α x * z x) x ∧ HasDerivAt z (β x * u x) x)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      exp (abs (∫ x in s..t, |α x| + |β x|)) := by
  have hderiv (x : ℝ) (hx : x ∈ Icc l r) :
      HasDerivAt (fun y => u y ^ 2 + z y ^ 2)
        (2 * (α x + β x) * (u x * z x)) x :=
    (((hd x hx).1.pow 2).add ((hd x hx).2.pow 2)).congr_deriv (by ring)
  have hbound (x : ℝ) (_hx : x ∈ Icc l r) :
      |2 * (α x + β x) * (u x * z x)| ≤
        (|α x| + |β x|) * (u x ^ 2 + z x ^ 2) := by
    have huv : 2 * |u x * z x| ≤ u x ^ 2 + z x ^ 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|u x| - |z x|), sq_abs (u x), sq_abs (z x)]
    calc
      _ = 2 * |α x + β x| * |u x * z x| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (|α x| + |β x|) * |u x * z x| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)) (abs_nonneg _)
      _ = (|α x| + |β x|) * (2 * |u x * z x|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left huv (add_nonneg (abs_nonneg _) (abs_nonneg _))
  exact gronwall_integral_exp hlr (hα.abs.add hβ.abs)
    (fun x _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hderiv hbound hs ht

def outerCompactCost (D : ReferenceData) (l r J S R : ℝ) : ℝ :=
  S * (∫ x in l..r, (D.w x)⁻¹) +
    (J * R) * (∫ x in l..r, |deriv D.w x| / x)

theorem outerCompactCost_nonneg {D : ReferenceData} {l r J S R : ℝ}
    (hD : RadialProfileGeometry D) (hlr : l ≤ r) (hsub : Icc l r ⊆ radialCore D)
    (hJ : 0 ≤ J) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    0 ≤ outerCompactCost D l r J S R := by
  have hi : 0 ≤ ∫ x in l..r, (D.w x)⁻¹ := intervalIntegral.integral_nonneg hlr
    (fun x hx => inv_nonneg.mpr (hD.2.2.2.2.1 x (hsub hx)).le)
  have hj : 0 ≤ ∫ x in l..r, |deriv D.w x| / x := intervalIntegral.integral_nonneg hlr
    (fun x hx => div_nonneg (abs_nonneg _) (hD.1.trans (hsub hx).1).le)
  exact add_nonneg (mul_nonneg hS hi) (mul_nonneg (mul_nonneg hJ hR) hj)

theorem outer_compact_state_energy {D : ReferenceData} {l r a b j scale J S R s t : ℝ}
    {u z : ℝ → ℝ} (hD : RadialProfileGeometry D) (hlr : l ≤ r)
    (hsub : Icc l r ⊆ radialCore D) (hab : a ≤ b) (hsmall : Icc a b ⊆ Icc l r)
    (hscale : 0 < scale) (hj : j ^ 2 ≤ J) (hhi : scale ≤ S) (hlo : 1 / scale ≤ R)
    (hd : ∀ x ∈ Icc a b, HasDerivAt u (scale / D.w x * z x) x ∧
      HasDerivAt z (j ^ 2 * deriv D.w x / (scale * x) * u x) x)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) * exp (outerCompactCost D l r J S R) := by
  let α : ℝ → ℝ := fun x => scale / D.w x
  let β : ℝ → ℝ := fun x => j ^ 2 * deriv D.w x / (scale * x)
  have hc := outerPhysical_coefficients_continuous hD hscale hsub j
  have hκ : ContinuousOn (fun x => |α x| + |β x|) (Icc l r) := hc.1.abs.add hc.2.abs
  have hfull := outer_abs_integral_le_whole hlr hκ
    (fun x _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (hsmall hs) (hsmall ht)
  have henergy := outer_signed_state_energy_transfer hab (hc.1.mono hsmall)
    (hc.2.mono hsmall) hd hs ht
  have hwp (x : ℝ) (hx : x ∈ Icc l r) : 0 < D.w x := hD.2.2.2.2.1 x (hsub hx)
  have hxp (x : ℝ) (hx : x ∈ Icc l r) : 0 < x := hD.1.trans (hsub hx).1
  have hw := hD.2.2.1.1
  have hdc : Continuous (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hIi : IntervalIntegrable (fun x => (D.w x)⁻¹) volume l r :=
    (hw.continuous.continuousOn.inv₀ (fun x hx => (hwp x hx).ne')).intervalIntegrable_of_Icc hlr
  have hJi : IntervalIntegrable (fun x => |deriv D.w x| / x) volume l r :=
    (hdc.abs.continuousOn.div continuousOn_id (fun x hx => (hxp x hx).ne')).intervalIntegrable_of_Icc hlr
  have hI₀ : 0 ≤ ∫ x in l..r, (D.w x)⁻¹ :=
    intervalIntegral.integral_nonneg hlr (fun x hx => inv_nonneg.mpr (hwp x hx).le)
  have hJ₀ : 0 ≤ ∫ x in l..r, |deriv D.w x| / x :=
    intervalIntegral.integral_nonneg hlr (fun x hx => div_nonneg (abs_nonneg _) (hxp x hx).le)
  have hcoeff : j ^ 2 / scale ≤ J * R := by
    have hJ : 0 ≤ J := (sq_nonneg j).trans hj
    simpa only [div_eq_mul_inv, one_mul, one_div] using
      mul_le_mul hj hlo (div_pos zero_lt_one hscale).le hJ
  have hsplit : (∫ x in l..r, |α x| + |β x|) =
      scale * (∫ x in l..r, (D.w x)⁻¹) +
        (j ^ 2 / scale) * (∫ x in l..r, |deriv D.w x| / x) := by
    calc
      _ = ∫ x in l..r, scale * (D.w x)⁻¹ + (j ^ 2 / scale) * (|deriv D.w x| / x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hlr] at hx
        dsimp only [α, β]
        simp only [abs_div, abs_mul, abs_inv, abs_of_pos hscale, abs_of_pos (hwp x hx),
          abs_of_pos (hxp x hx), abs_of_nonneg (sq_nonneg j), div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hIi.const_mul scale) (hJi.const_mul (j ^ 2 / scale)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcost : (∫ x in l..r, |α x| + |β x|) ≤ outerCompactCost D l r J S R := by
    rw [hsplit]
    exact add_le_add (mul_le_mul_of_nonneg_right hhi hI₀) (mul_le_mul_of_nonneg_right hcoeff hJ₀)
  exact henergy.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (hfull.trans hcost)) (by positivity))

theorem radialFrequencyBand_index_pos {T : MorseChainData} {C : ℝ} {n j : ℕ}
    (hband : radialFrequencyBand T C n j) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  have hz : radialFrequencyThreshold T C 0 = 0 := by
    simp only [radialFrequencyThreshold, radialQ, Nat.cast_zero,
      zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0), zero_mul, mul_zero, zero_div]
  have hj := hband.2.2
  rw [hz] at hj
  exact (not_lt_of_ge (Nat.cast_nonneg j)) hj

end ContinuousFlexibility.Radial
