import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The full physical circle and the half-period source model

Source fields have period `pi`, while `RadialTest` allows period `2*pi`.
The full-period physical mean agrees with the half-period mean for a
periodic integrand.  For a general physical test its half-period average
must be used before making that replacement.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The two normalizations agree on genuinely half-periodic integrands. -/
theorem n06_radialAngularMean_eq_angularMean {f : ℝ → ℝ}
    (hf : Function.Periodic f Real.pi)
    (hint : IntervalIntegrable f volume 0 Real.pi) :
    radialAngularMean f = angularMean f := by
  have hsecond : (∫ θ in Real.pi..2 * Real.pi, f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    simpa only [zero_add, ← two_mul] using hf.intervalIntegral_add_eq Real.pi 0
  have hsecondInt : IntervalIntegrable f volume Real.pi (2 * Real.pi) :=
    hf.intervalIntegrable₀ Real.pi_ne_zero hint _ _
  have hdouble : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint hsecondInt, hsecond]
    ring
  unfold radialAngularMean angularMean
  rw [hdouble]
  field_simp [Real.pi_ne_zero] <;> ring

theorem n06_radialAngularMean_eq_angularMean_of_continuous {f : ℝ → ℝ}
    (hf : Function.Periodic f Real.pi) (hc : Continuous f) :
    radialAngularMean f = angularMean f :=
  n06_radialAngularMean_eq_angularMean hf (hc.intervalIntegrable _ _)

/-- Projection of a full-period angular test onto its half-period part. -/
def n06_halfPeriodAverage (φ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (φ θ + φ (θ + Real.pi)) / 2

theorem n06_halfPeriodAverage_periodic {φ : ℝ → ℝ}
    (hφ : Function.Periodic φ (2 * Real.pi)) :
    Function.Periodic (n06_halfPeriodAverage φ) Real.pi := by
  intro θ
  have hs : φ (θ + Real.pi + Real.pi) = φ θ := by
    rw [show θ + Real.pi + Real.pi = θ + 2 * Real.pi by ring]
    exact hφ θ
  change (φ (θ + Real.pi) + φ (θ + Real.pi + Real.pi)) / 2 =
    (φ θ + φ (θ + Real.pi)) / 2
  rw [hs]
  ring

theorem n06_halfPeriodAverage_eq {φ : ℝ → ℝ}
    (hφ : Function.Periodic φ Real.pi) : n06_halfPeriodAverage φ = φ := by
  funext θ
  change (φ θ + φ (θ + Real.pi)) / 2 = φ θ
  rw [hφ θ]
  ring

/-- Splitting the full circle and translating its second half gives the
correct pairing with a general test.  No periodicity of the test is needed
for this integral identity. -/
theorem n06_radialAngularMean_pairing {u φ : ℝ → ℝ}
    (hu : Function.Periodic u Real.pi)
    (hint : IntervalIntegrable (fun θ => u θ * φ θ) volume 0 (2 * Real.pi)) :
    radialAngularMean (fun θ => u θ * φ θ) =
      angularMean (fun θ => u θ * n06_halfPeriodAverage φ θ) := by
  have hfirst : IntervalIntegrable (fun θ => u θ * φ θ) volume 0 Real.pi := by
    apply hint.mono_set
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hsecond : IntervalIntegrable (fun θ => u θ * φ θ) volume Real.pi (2 * Real.pi) := by
    apply hint.mono_set
    rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi),
      uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact Icc_subset_Icc Real.pi_pos.le le_rfl
  have hshiftInt : IntervalIntegrable (fun θ => u θ * φ (θ + Real.pi))
      volume 0 Real.pi := by
    simpa only [sub_self, show 2 * Real.pi - Real.pi = Real.pi by ring, hu] using
      hsecond.comp_add_right Real.pi
  have hshift : (∫ θ in (0 : ℝ)..Real.pi, u θ * φ (θ + Real.pi)) =
      ∫ θ in Real.pi..2 * Real.pi, u θ * φ θ := by
    simpa only [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring, hu] using
      (intervalIntegral.integral_comp_add_right (fun θ => u θ * φ θ) Real.pi
        (a := (0 : ℝ)) (b := Real.pi))
  have haverage : (∫ θ in (0 : ℝ)..Real.pi, u θ * n06_halfPeriodAverage φ θ) =
      ((∫ θ in (0 : ℝ)..Real.pi, u θ * φ θ) +
        ∫ θ in (0 : ℝ)..Real.pi, u θ * φ (θ + Real.pi)) / 2 := by
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi, (u θ * φ θ + u θ * φ (θ + Real.pi)) / 2 := by
        congr 1
        funext θ
        unfold n06_halfPeriodAverage
        ring
      _ = _ := by rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add hfirst hshiftInt]
  have hfull : (∫ θ in (0 : ℝ)..2 * Real.pi, u θ * φ θ) =
      (∫ θ in (0 : ℝ)..Real.pi, u θ * φ θ) +
        ∫ θ in (0 : ℝ)..Real.pi, u θ * φ (θ + Real.pi) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond, hshift]
  unfold radialAngularMean angularMean
  rw [hfull, haverage]
  field_simp [Real.pi_ne_zero] <;> ring

theorem n06_radialAngularMean_pairing_of_continuous {u φ : ℝ → ℝ}
    (hu : Function.Periodic u Real.pi) (huc : Continuous u) (hφc : Continuous φ) :
    radialAngularMean (fun θ => u θ * φ θ) =
      angularMean (fun θ => u θ * n06_halfPeriodAverage φ θ) :=
  n06_radialAngularMean_pairing hu ((huc.mul hφc).intervalIntegrable _ _)

/-- The same averaging operation on a physical test preserves its radial
support and all spatial regularity. -/
def n06_radialTestAverage (φ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  n06_halfPeriodAverage (fun θ => φ (p.1, θ)) p.2

theorem n06_radialTestAverage_periodic {φ : PolarPoint → ℝ}
    (hφ : Function.Periodic φ (0, 2 * Real.pi)) :
    Function.Periodic (n06_radialTestAverage φ) (0, Real.pi) := by
  intro p
  have hr : Function.Periodic (fun θ => φ (p.1, θ)) (2 * Real.pi) := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hφ (p.1, θ)
  simpa only [n06_radialTestAverage, Prod.fst_add, Prod.snd_add, add_zero] using
    n06_halfPeriodAverage_periodic hr p.2

theorem n06_radialTestAverage_test {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hφ : RadialTest D φ) : RadialTest D (n06_radialTestAverage φ) := by
  have hs : ContDiff ℝ ∞ (n06_radialTestAverage φ) := by
    have he : n06_radialTestAverage φ =
        (fun p : PolarPoint => (φ p + φ (p + (0, Real.pi))) / 2) := by
      funext p
      simp only [n06_radialTestAverage, n06_halfPeriodAverage, Prod.add_def,
        add_zero, Prod.mk.eta]
    rw [he]
    exact (hφ.1.add (hφ.1.comp (contDiff_id.add contDiff_const))).div_const 2
  have hp := n06_radialTestAverage_periodic hφ.2.1
  have hp₂ : Function.Periodic (n06_radialTestAverage φ) (0, 2 * Real.pi) := by
    simpa only [Prod.mk_add_mk, zero_add, ← two_mul] using hp.add_period hp
  refine ⟨hs, hp₂, ?_⟩
  obtain ⟨K, hK, hKD, hz⟩ := hφ.2.2
  refine ⟨K, hK, hKD, ?_⟩
  intro r hr θ
  simp only [n06_radialTestAverage, n06_halfPeriodAverage, hz r hr, zero_add, zero_div]

theorem n06_radialTestAverage_eq {φ : PolarPoint → ℝ}
    (hφ : Function.Periodic φ (0, Real.pi)) : n06_radialTestAverage φ = φ := by
  funext p
  have hr : Function.Periodic (fun θ => φ (p.1, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hφ (p.1, θ)
  exact congrFun (n06_halfPeriodAverage_eq hr) p.2

end ContinuousFlexibility.Statements
