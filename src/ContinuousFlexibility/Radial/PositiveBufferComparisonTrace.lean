import ContinuousFlexibility.Radial.PositiveBufferComparison
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A sharp L²-to-cut estimate through a positive half-line

The exponential comparison may be based at every point of a preceding
layer.  Integrating over a layer of length `1 / m` gives the `sqrt m`
trace cost without using a derivative norm.  This is the second
attenuation factor in the matrix of cut values.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

/-- The half-line attenuation estimate can be based at any later point
of the same homogeneous region. -/
theorem positiveBuffer_halfline_abs_relative_bound {a M m x y : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ t ∈ Ioi a, HasDerivAt u (du t) t)
    (hdu : ∀ t ∈ Ioi a, HasDerivAt du (q t * u t) t)
    (hq : ∀ t ∈ Ioi a, m ^ 2 ≤ q t)
    (hbound : ∀ t ∈ Ici a, |u t| ≤ M)
    (hx : a ≤ x) (hxy : x ≤ y) :
    |u y| ≤ |u x| * exp (-m * (y - x)) := by
  apply positiveBuffer_halfline_abs_exponential_bound (a := x) hm hM
    (hc.mono (fun _ ht => hx.trans ht))
    (fun t ht => hu t (hx.trans_lt ht))
    (fun t ht => hdu t (hx.trans_lt ht))
    (fun t ht => hq t (hx.trans_lt ht))
    (fun t ht => hbound t (hx.trans ht)) y hxy

/-- Integrating the shifted exponential comparison over a preceding
layer gives a quantitative scalar trace estimate. -/
theorem positiveBuffer_halfline_square_trace_bound {a M m r δ c σ : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ t ∈ Ioi a, HasDerivAt u (du t) t)
    (hdu : ∀ t ∈ Ioi a, HasDerivAt du (q t * u t) t)
    (hq : ∀ t ∈ Ioi a, m ^ 2 ≤ q t)
    (hbound : ∀ t ∈ Ici a, |u t| ≤ M)
    (hr : a ≤ r) (hδ : 0 < δ) (hcut : r + δ ≤ c)
    (haction : σ ≤ m * (c - (r + δ))) :
    δ * u c ^ 2 ≤ exp (-σ) ^ 2 * (∫ t in r..r + δ, u t ^ 2) := by
  have hrδ : r ≤ r + δ := by linarith
  have hucc : ContinuousOn u (Icc r (r + δ)) :=
    hc.mono (fun _ ht => hr.trans ht.1)
  have hint : IntervalIntegrable (fun t => exp (-σ) ^ 2 * u t ^ 2)
      volume r (r + δ) :=
    (continuousOn_const.mul (hucc.pow 2)).intervalIntegrable_of_Icc hrδ
  have hp (t : ℝ) (ht : t ∈ Icc r (r + δ)) :
      u c ^ 2 ≤ exp (-σ) ^ 2 * u t ^ 2 := by
    have htc : t ≤ c := ht.2.trans hcut
    have he := positiveBuffer_halfline_abs_relative_bound hm hM hc hu hdu hq hbound
      (hr.trans ht.1) htc
    have hexp : exp (-m * (c - t)) ≤ exp (-σ) := by
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left ht.2 hm.le
      nlinarith
    have hle : |u c| ≤ |u t| * exp (-σ) :=
      he.trans (mul_le_mul_of_nonneg_left hexp (abs_nonneg _))
    calc
      u c ^ 2 = |u c| ^ 2 := (sq_abs _).symm
      _ ≤ (|u t| * exp (-σ)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _) (exp_pos _).le)).mpr hle
      _ = exp (-σ) ^ 2 * u t ^ 2 := by rw [mul_pow, sq_abs]; ring
  have hmono := intervalIntegral.integral_mono_on hrδ
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => u c ^ 2) volume r (r + δ))
    hint hp
  simpa only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    smul_eq_mul, show r + δ - r = δ by ring] using hmono

/-- A classical representative on a half-line has no more L² mass on
a finite subinterval than its actual global L² element. -/
theorem positiveBuffer_interval_square_le_l2_norm {a r δ : ℝ} {u : ℝ → ℝ}
    (f : Lp ℝ 2 volume) (hr : a ≤ r) (hδ : 0 ≤ δ)
    (hrep : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ici a)] u) :
    (∫ t in r..r + δ, u t ^ 2) ≤ ‖f‖ ^ 2 := by
  have hrδ : r ≤ r + δ := by linarith
  have hrepI : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioc r (r + δ))] u :=
    ae_restrict_of_ae_restrict_of_subset (fun _ ht => hr.trans ht.1.le) hrep
  have hnorm : ‖f‖ ^ 2 = ∫ t : ℝ, f t ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by simp only [RCLike.inner_apply, conj_trivial, pow_two])
  rw [intervalIntegral.integral_of_le hrδ, hnorm]
  calc
    (∫ t in Ioc r (r + δ), u t ^ 2) = ∫ t in Ioc r (r + δ), f t ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hrepI] with t ht
      rw [ht]
    _ ≤ ∫ t : ℝ, f t ^ 2 :=
      setIntegral_le_integral (Lp.memLp f).integrable_sq
        (Eventually.of_forall (fun _ => sq_nonneg _))

/-- The sharp cut estimate after action `σ`, measured from a preceding
layer of length `1 / m`.  The full inverse enters later only through
the actual norm `‖f‖`; no energy or derivative norm occurs. -/
theorem positiveBuffer_halfline_l2_trace_bound {a M m r c σ : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ t ∈ Ioi a, HasDerivAt u (du t) t)
    (hdu : ∀ t ∈ Ioi a, HasDerivAt du (q t * u t) t)
    (hq : ∀ t ∈ Ioi a, m ^ 2 ≤ q t)
    (hbound : ∀ t ∈ Ici a, |u t| ≤ M)
    (f : Lp ℝ 2 volume)
    (hrep : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ici a)] u)
    (hr : a ≤ r) (hcut : r + 1 / m ≤ c)
    (haction : σ ≤ m * (c - (r + 1 / m))) :
    |u c| ≤ sqrt m * exp (-σ) * ‖f‖ := by
  have hδ : 0 < 1 / m := one_div_pos.mpr hm
  have hscalar := positiveBuffer_halfline_square_trace_bound hm hM hc hu hdu hq hbound
    hr hδ hcut haction
  have hmass := positiveBuffer_interval_square_le_l2_norm f hr hδ.le hrep
  have hscaled : (1 / m) * u c ^ 2 ≤ exp (-σ) ^ 2 * ‖f‖ ^ 2 :=
    hscalar.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _))
  have hsq : u c ^ 2 ≤ m * (exp (-σ) ^ 2 * ‖f‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hscaled hm.le
    simpa only [← mul_assoc, mul_one_div_cancel hm.ne', one_mul] using h
  apply (sq_le_sq₀ (abs_nonneg (u c))
    (mul_nonneg (mul_nonneg (sqrt_nonneg _) (exp_pos _).le) (norm_nonneg _))).mp
  rw [sq_abs, mul_pow, mul_pow, sq_sqrt hm.le]
  simpa only [mul_assoc] using hsq

end ContinuousFlexibility.Radial
