import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Energy and conormal identities for a positive buffer

The functions and their first derivatives are explicit classical representatives.
All differentiability assumptions are local to the interval, so these lemmas apply
to a finite-buffer minimizer before choosing any global smooth extension.
-/

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter
open scoped Topology

/-- On a finite interval a homogeneous Schrödinger solution has energy equal
to its boundary flux. This treats both orientations of the buffer at once. -/
theorem positiveBuffer_energy_eq_flux {a b : ℝ} (hab : a ≤ b)
    {u d V : ℝ → ℝ} (hu : ContinuousOn u (Icc a b))
    (hd : ContinuousOn d (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u (d x) x)
    (hd' : ∀ x ∈ Ioo a b, HasDerivAt d (V x * u x) x) :
    (∫ x in a..b, d x ^ 2 + V x * u x ^ 2) =
      u b * d b - u a * d a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hu.mul hd)
  · intro x hx
    convert (hu' x hx).mul (hd' x hx) using 1 <;> ring
  · exact ((hd.pow 2).add (hV.mul (hu.pow 2))).intervalIntegrable_of_Icc hab

/-- Completing the square gives the oriented trace bound. No differential
equation is required: it holds for every competing energy field. -/
theorem positiveBuffer_oriented_trace_energy {a b m : ℝ} (hab : a ≤ b)
    {u d V : ℝ → ℝ} (hu : ContinuousOn u (Icc a b))
    (hd : ContinuousOn d (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u (d x) x)
    (hVm : ∀ x ∈ Icc a b, m ^ 2 ≤ V x) :
    m * (u a ^ 2 - u b ^ 2) ≤ ∫ x in a..b, d x ^ 2 + V x * u x ^ 2 := by
  have hleft : IntervalIntegrable (fun x => -2 * m * u x * d x) volume a b :=
    ((continuousOn_const.mul hu).mul hd).intervalIntegrable_of_Icc hab
  have hright : IntervalIntegrable (fun x => d x ^ 2 + V x * u x ^ 2) volume a b :=
    ((hd.pow 2).add (hV.mul (hu.pow 2))).intervalIntegrable_of_Icc hab
  have hid : (∫ x in a..b, -2 * m * u x * d x) = m * (u a ^ 2 - u b ^ 2) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      ((hu.pow 2).const_mul (-m)) (f' := fun x => -2 * m * u x * d x)
      (fun x hx => by
        convert ((hu' x hx).pow 2).const_mul (-m) using 1 <;> ring) hleft
    convert h using 1 <;> simp only [Pi.pow_apply] <;> ring
  rw [← hid]
  apply intervalIntegral.integral_mono_on hab hleft hright
  intro x hx
  have hv := mul_le_mul_of_nonneg_right (hVm x hx) (sq_nonneg (u x))
  nlinarith [sq_nonneg (d x + m * u x)]

/-- The trace bound is independent of which endpoint carries the boundary
value; the same lemma is used at the two ends of the retained interval. -/
theorem positiveBuffer_trace_energy {a b m : ℝ} (hab : a ≤ b)
    {u d V : ℝ → ℝ} (hu : ContinuousOn u (Icc a b))
    (hd : ContinuousOn d (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u (d x) x)
    (hVm : ∀ x ∈ Icc a b, m ^ 2 ≤ V x) :
    |m * (u a ^ 2 - u b ^ 2)| ≤ ∫ x in a..b, d x ^ 2 + V x * u x ^ 2 := by
  apply abs_le.mpr
  constructor
  · have h := positiveBuffer_oriented_trace_energy (m := -m) hab hu hd hV hu'
      (fun x hx => by simpa only [neg_sq] using hVm x hx)
    linarith
  · exact positiveBuffer_oriented_trace_energy hab hu hd hV hu' hVm

/-- A unit endpoint value with zero at the other end costs at least the
barrier mass in energy, uniformly in the buffer length. -/
theorem positiveBuffer_unit_trace_energy {a b m : ℝ} (hab : a ≤ b) (hm : 0 ≤ m)
    {u d V : ℝ → ℝ} (hu : ContinuousOn u (Icc a b))
    (hd : ContinuousOn d (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u (d x) x)
    (hVm : ∀ x ∈ Icc a b, m ^ 2 ≤ V x)
    (hboundary : (u a = 1 ∧ u b = 0) ∨ (u a = 0 ∧ u b = 1)) :
    m ≤ ∫ x in a..b, d x ^ 2 + V x * u x ^ 2 := by
  have h := positiveBuffer_trace_energy hab hu hd hV hu' hVm
  rcases hboundary with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa only [ha, hb, one_pow, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
      mul_one, abs_of_nonneg hm] using h
  · simpa only [ha, hb, one_pow, zero_pow (by norm_num : 2 ≠ 0), zero_sub,
      mul_neg, mul_one, abs_neg, abs_of_nonneg hm] using h

/-- Passing to the infinite endpoint preserves the sharp lower trace bound.
The decay hypothesis is a property of the classical finite-energy solution,
not an assertion about an arbitrary representative of an `L²` class. -/
theorem positiveBuffer_halfline_trace_energy {a m : ℝ}
    {u d V : ℝ → ℝ} (hu : ContinuousOn u (Ici a))
    (hd : ContinuousOn d (Ici a)) (hV : ContinuousOn V (Ici a))
    (hu' : ∀ x ∈ Ioi a, HasDerivAt u (d x) x)
    (hVm : ∀ x ∈ Ici a, m ^ 2 ≤ V x)
    (hE : IntegrableOn (fun x => d x ^ 2 + V x * u x ^ 2) (Ioi a) volume)
    (hu0 : Tendsto u atTop (𝓝 0)) :
    m * u a ^ 2 ≤ ∫ x in Ioi a, d x ^ 2 + V x * u x ^ 2 := by
  have ht : Tendsto (fun b => m * (u a ^ 2 - u b ^ 2)) atTop (𝓝 (m * u a ^ 2)) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using
      tendsto_const_nhds.mul (tendsto_const_nhds.sub (hu0.pow 2))
  apply le_of_tendsto_of_tendsto ht (intervalIntegral_tendsto_integral_Ioi a hE tendsto_id)
  filter_upwards [eventually_ge_atTop a] with b hb
  exact positiveBuffer_oriented_trace_energy hb (hu.mono Icc_subset_Ici_self)
    (hd.mono Icc_subset_Ici_self) (hV.mono Icc_subset_Ici_self)
    (fun x hx => hu' x hx.1) (fun x hx => hVm x hx.1)

/-- The exterior energy equals the inward conormal at the cut, once the
boundary product at infinity has been shown to vanish. -/
theorem positiveBuffer_halfline_energy_eq_flux {a : ℝ}
    {u d V : ℝ → ℝ} (hu : ContinuousOn u (Ici a))
    (hd : ContinuousOn d (Ici a))
    (hu' : ∀ x ∈ Ioi a, HasDerivAt u (d x) x)
    (hd' : ∀ x ∈ Ioi a, HasDerivAt d (V x * u x) x)
    (hE : IntegrableOn (fun x => d x ^ 2 + V x * u x ^ 2) (Ioi a) volume)
    (hzero : Tendsto (fun x => u x * d x) atTop (𝓝 0)) :
    (∫ x in Ioi a, d x ^ 2 + V x * u x ^ 2) = -(u a * d a) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto ((hu.mul hd) a (le_refl a))
    (f' := fun x => d x ^ 2 + V x * u x ^ 2)
    (fun x hx => by convert (hu' x hx).mul (hd' x hx) using 1 <;> ring) hE hzero
  simpa only [zero_sub] using h

end ContinuousFlexibility.Radial
