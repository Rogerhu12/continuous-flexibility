import ContinuousFlexibility.Analysis.CircleReturnFourier
import ContinuousFlexibility.Analysis.CircleReturnSeries
import ContinuousFlexibility.Analysis.CircleReturnUniqueness

/-!
# The return inverse on actual smooth circle functions

Every smooth, even, zero-mean function of period pi has a unique smooth odd
preimage under the return operator when its travel angle has a positive
small-divisor margin.  Existence uses the integral Fourier expansion proved
in `CircleReturnFourier`; uniqueness applies to all continuous odd functions.

The range lemmas verify the converse direction as well: the return operator
takes every smooth odd function of period pi to the stated target class.
No Fourier-expansion hypothesis is imposed on either class of functions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ContDiff

/-- A positive small-divisor margin excludes rational travel angles. -/
theorem irrational_travel_of_smallDivisor {T γ : ℝ} (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|) :
    Irrational (T / Real.pi) := by
  by_contra hrat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hdenNat : 1 ≤ q.den := q.den_pos
  rw [Rat.cast_def] at hq
  have hcross := (div_eq_div_iff Real.pi_ne_zero hden.ne').mp hq
  have hangle : (q.den : ℝ) * T = (q.num : ℝ) * Real.pi := by
    simpa only [mul_comm] using hcross
  have hsin : Real.sin ((q.den : ℝ) * T) = 0 := by
    rw [hangle]
    exact Real.sin_int_mul_pi q.num
  have hpos : 0 < |Real.sin ((q.den : ℝ) * T)| :=
    lt_of_lt_of_le (div_pos hγ hden) (hT q.den hdenNat)
  rw [hsin, abs_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- The return operator preserves genuine smoothness. -/
theorem contDiff_circleReturnShift {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (T : ℝ) :
    ContDiff ℝ ∞ (circleReturnShift T v) := by
  unfold circleReturnShift circleReturnEven
  exact ((hv.comp (contDiff_id.add contDiff_const)).add
    (hv.comp (contDiff_id.neg.add contDiff_const))).div_const 2

/-- Its value is even, by the defining parity projection. -/
theorem even_circleReturnShift (T : ℝ) (v : ℝ → ℝ) :
    Function.Even (circleReturnShift T v) :=
  circleReturnEven_even (fun θ => v (θ + T))

/-- The shift difference of an odd pi-periodic function is pi-periodic. -/
theorem periodic_circleReturnShift {v : ℝ → ℝ}
    (hp : Function.Periodic v Real.pi) (ho : ∀ θ, v (-θ) = -v θ) (T : ℝ) :
    Function.Periodic (circleReturnShift T v) Real.pi := by
  intro θ
  rw [circleReturnShift_odd ho, circleReturnShift_odd ho]
  have hplus : v (θ + Real.pi + T) = v (θ + T) := by
    convert hp (θ + T) using 1 <;> congr 1 <;> ring
  have hminus : v (θ + Real.pi - T) = v (θ - T) := by
    convert hp (θ - T) using 1 <;> congr 1 <;> ring
  rw [hplus, hminus]

/-- Translation does not change the integral over a full period. -/
theorem circle_periodic_shift_integral {v : ℝ → ℝ}
    (hp : Function.Periodic v Real.pi) (t : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, v (θ + t)) =
      ∫ θ in (0 : ℝ)..Real.pi, v θ := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm Real.pi t] using hp.intervalIntegral_add_eq t 0

/-- The odd return operator has zero actual angular integral. -/
theorem integral_circleReturnShift_eq_zero {v : ℝ → ℝ}
    (hv : Continuous v) (hp : Function.Periodic v Real.pi)
    (ho : ∀ θ, v (-θ) = -v θ) (T : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi, circleReturnShift T v θ = 0 := by
  have hiPlus : IntervalIntegrable (fun θ : ℝ => v (θ + T)) volume 0 Real.pi := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq] using
      ((hv.comp (continuous_id.add continuous_const)).intervalIntegrable 0 Real.pi)
  have hiMinus : IntervalIntegrable (fun θ : ℝ => v (θ - T)) volume 0 Real.pi := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq] using
      ((hv.comp (continuous_id.sub continuous_const)).intervalIntegrable 0 Real.pi)
  simp_rw [circleReturnShift_odd ho]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hiPlus hiMinus,
    circle_periodic_shift_integral hp T]
  have hminus : (∫ θ in (0 : ℝ)..Real.pi, v (θ - T)) =
      ∫ θ in (0 : ℝ)..Real.pi, v θ := by
    simpa only [sub_eq_add_neg] using circle_periodic_shift_integral hp (-T)
  rw [hminus, sub_self, zero_div]

/-- Every function in the smooth odd domain maps into the smooth even
zero-mean target; this is the forward half of the correspondence. -/
theorem circleReturnShift_output_properties {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : Function.Periodic v Real.pi)
    (ho : ∀ θ, v (-θ) = -v θ) (T : ℝ) :
    ContDiff ℝ ∞ (circleReturnShift T v) ∧
      Function.Periodic (circleReturnShift T v) Real.pi ∧
      Function.Even (circleReturnShift T v) ∧
      (∫ θ in (0 : ℝ)..Real.pi, circleReturnShift T v θ) = 0 :=
  ⟨contDiff_circleReturnShift hv T, periodic_circleReturnShift hp ho T,
    even_circleReturnShift T v, integral_circleReturnShift_eq_zero hv.continuous hp ho T⟩

/-- A genuine smooth odd solution of the return equation exists for every
smooth even zero-mean target.  The input function has no assumed expansion. -/
theorem exists_smooth_circleReturn_inverse {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ θ in (0 : ℝ)..Real.pi, f θ = 0) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v Real.pi ∧
      (∀ θ, v (-θ) = -v θ) ∧ circleReturnShift T v = f := by
  obtain ⟨c, hc0, hc, hceven, hseries⟩ :=
    exists_rapid_circleCosine_expansion_pi hf hp he hm
  refine ⟨circleReturnInverseSeries c T,
    contDiff_circleReturnInverseSeries hγ hT hc,
    circleReturnInverseSeries_periodic_pi hceven T,
    circleReturnInverseSeries_odd c T, ?_⟩
  funext θ
  exact (circleReturnShift_inverseSeries hγ hT
    (by simpa only [pow_one] using hc 1) hc0 θ).trans (hseries θ).symm

/-- The smooth odd and smooth even zero-mean classes are in one-to-one
correspondence under the actual return operator.  Together with
`circleReturnShift_output_properties`, this supplies both inverse laws. -/
theorem existsUnique_smooth_circleReturn_inverse {f : ℝ → ℝ} {T γ : ℝ}
    (hγ : 0 < γ)
    (hT : ∀ j : ℕ, 1 ≤ j → γ / j ≤ |Real.sin (j * T)|)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Real.pi)
    (he : Function.Even f) (hm : ∫ θ in (0 : ℝ)..Real.pi, f θ = 0) :
    ∃! v : ℝ → ℝ, ContDiff ℝ ∞ v ∧ Function.Periodic v Real.pi ∧
      (∀ θ, v (-θ) = -v θ) ∧ circleReturnShift T v = f := by
  obtain ⟨v, hvs, hvp, hvo, hvf⟩ := exists_smooth_circleReturn_inverse hγ hT hf hp he hm
  refine ⟨v, ⟨hvs, hvp, hvo, hvf⟩, ?_⟩
  intro u hu
  apply circleReturnShift_injective_on_odd hu.1.continuous hvs.continuous
    hu.2.1 hvp hu.2.2.1 hvo (irrational_travel_of_smallDivisor hγ hT)
  intro θ
  rw [hu.2.2.2, hvf]

end ContinuousFlexibility.Analysis
