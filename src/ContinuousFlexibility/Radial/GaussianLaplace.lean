module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The convergent Laplace--Gaussian moments of the central radius

The integral is over the actual positive half-line. Euler's Gamma
integrability gives a global majorant; differentiation is justified by
the dominated-derivative theorem, rather than postulated for the integral.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def gaussianLaplaceKernel (β x t : ℝ) : ℝ :=
  t ^ (β - 1) * exp (-t ^ 2 / 2 + sqrt 2 * x * t)

def gaussianLaplaceMoment (β x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), gaussianLaplaceKernel β x t

theorem gaussianLaplaceKernel_pos (β x : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < gaussianLaplaceKernel β x t :=
  mul_pos (rpow_pos_of_pos ht _) (exp_pos _)

theorem continuousOn_gaussianLaplaceKernel (β x : ℝ) :
    ContinuousOn (gaussianLaplaceKernel β x) (Ioi 0) := by
  apply (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).mul
  exact (((continuous_id.pow 2).neg.div_const 2).add
    ((continuous_const.mul continuous_const).mul continuous_id)).rexp.continuousOn

/-- Completing the square dominates the Gaussian by an exponential Gamma
integrand, even when the parameter `x` is large. -/
theorem gaussianLaplaceKernel_le_gamma (β x : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianLaplaceKernel β x t ≤
      exp ((sqrt 2 * x + 1) ^ 2 / 2) * (exp (-t) * t ^ (β - 1)) := by
  have he : -t ^ 2 / 2 + sqrt 2 * x * t ≤ (sqrt 2 * x + 1) ^ 2 / 2 - t := by
    nlinarith [sq_nonneg (t - (sqrt 2 * x + 1))]
  have hh := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (rpow_nonneg ht.le (β - 1))
  unfold gaussianLaplaceKernel
  convert hh using 1
  rw [exp_sub, exp_neg]
  ring

theorem integrableOn_gaussianLaplaceKernel {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    IntegrableOn (gaussianLaplaceKernel β x) (Ioi 0) := by
  apply ((GammaIntegral_convergent hβ).const_mul (exp ((sqrt 2 * x + 1) ^ 2 / 2))).mono'
    ((continuousOn_gaussianLaplaceKernel β x).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (gaussianLaplaceKernel_pos β x ht)]
  exact gaussianLaplaceKernel_le_gamma β x ht

theorem gaussianLaplaceMoment_pos {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    0 < gaussianLaplaceMoment β x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => (gaussianLaplaceKernel_pos β x ht).le))
    (integrableOn_gaussianLaplaceKernel hβ x)).mpr
  have hs : Function.support (gaussianLaplaceKernel β x) ∩ Ioi 0 = Ioi 0 := by
    ext t
    exact ⟨fun h => h.2, fun ht => ⟨(gaussianLaplaceKernel_pos β x ht).ne', ht⟩⟩
  rw [hs]
  simp

theorem gaussianLaplaceKernel_succ (β x : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianLaplaceKernel (β + 1) x t = t * gaussianLaplaceKernel β x t := by
  have hr : t ^ β = t ^ (β - 1) * t := by
    calc
      t ^ β = t ^ (β - 1 + 1) := by congr 1; ring
      _ = _ := rpow_add_one ht.ne' (β - 1)
  simp only [gaussianLaplaceKernel, add_sub_cancel_right, hr]
  ring

theorem gaussianLaplaceKernel_mono (β : ℝ) {x y t : ℝ} (hxy : x ≤ y) (ht : 0 < t) :
    gaussianLaplaceKernel β x t ≤ gaussianLaplaceKernel β y t := by
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg ht.le _)
  apply exp_le_exp.mpr
  have hs : 0 ≤ sqrt (2 : ℝ) := sqrt_nonneg _
  nlinarith [mul_nonneg hs ht.le, mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hs ht.le)]

theorem hasDerivAt_gaussianLaplaceKernel_parameter (β x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y => gaussianLaplaceKernel β y t)
      (sqrt 2 * gaussianLaplaceKernel (β + 1) x t) x := by
  rw [gaussianLaplaceKernel_succ β x ht]
  convert (((hasDerivAt_id x).const_mul (sqrt 2 * t)).const_add (-t ^ 2 / 2)).exp.const_mul
    (t ^ (β - 1)) using 1
  · funext y
    simp only [gaussianLaplaceKernel, id_eq]
    congr 1
    congr 1
    ring
  · unfold gaussianLaplaceKernel
    simp only [id_eq]
    ring_nf

/-- The first parameter derivative is an actual dominated differentiation
of the integral, valid for every positive moment exponent. -/
theorem hasDerivAt_gaussianLaplaceMoment {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (gaussianLaplaceMoment β)
      (sqrt 2 * gaussianLaplaceMoment (β + 1) x) x := by
  have hβ1 : 0 < β + 1 := by linarith
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := Iio (x + 1))
    (F := fun y t => gaussianLaplaceKernel β y t)
    (F' := fun y t => sqrt 2 * gaussianLaplaceKernel (β + 1) y t)
    (bound := fun t => sqrt 2 * gaussianLaplaceKernel (β + 1) (x + 1) t)
    (Iio_mem_nhds (by linarith : x < x + 1))
    (Eventually.of_forall (fun y =>
      (integrableOn_gaussianLaplaceKernel hβ y).aestronglyMeasurable))
    (integrableOn_gaussianLaplaceKernel hβ x)
    ((integrableOn_gaussianLaplaceKernel hβ1 x).const_mul (sqrt 2)).aestronglyMeasurable
    ?_ ((integrableOn_gaussianLaplaceKernel hβ1 (x + 1)).const_mul (sqrt 2)) ?_
  · change HasDerivAt (fun y => ∫ t in Ioi (0 : ℝ), gaussianLaplaceKernel β y t) _ x
    simpa only [gaussianLaplaceMoment, integral_const_mul] using hD.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    rw [Real.norm_eq_abs, abs_of_pos
      (mul_pos (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
        (gaussianLaplaceKernel_pos (β + 1) y ht))]
    exact mul_le_mul_of_nonneg_left (gaussianLaplaceKernel_mono (β + 1) hy.le ht)
      (sqrt_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y _
    exact hasDerivAt_gaussianLaplaceKernel_parameter β y ht

theorem deriv_gaussianLaplaceMoment {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    deriv (gaussianLaplaceMoment β) x = sqrt 2 * gaussianLaplaceMoment (β + 1) x :=
  (hasDerivAt_gaussianLaplaceMoment hβ x).deriv

/-- Every moment is genuinely smooth in the model coordinate. -/
theorem contDiff_gaussianLaplaceMoment {β : ℝ} (hβ : 0 < β) :
    ContDiff ℝ ∞ (gaussianLaplaceMoment β) := by
  have hn : ∀ n : ℕ, ∀ b : ℝ, 0 < b → ContDiff ℝ n (gaussianLaplaceMoment b) := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have hd : Differentiable ℝ (gaussianLaplaceMoment b) :=
        fun x => (hasDerivAt_gaussianLaplaceMoment hb x).differentiableAt
      exact contDiff_zero.mpr hd.continuous
    | succ n ih =>
      intro b hb
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hasDerivAt_gaussianLaplaceMoment hb x).differentiableAt, by simp, ?_⟩
      have hd : deriv (gaussianLaplaceMoment b) =
          fun x => sqrt 2 * gaussianLaplaceMoment (b + 1) x :=
        funext (deriv_gaussianLaplaceMoment hb)
      rw [hd]
      exact contDiff_const.mul (ih (b + 1) (by linarith))
  exact contDiff_infty.mpr (fun n => hn n β hβ)

/-- The integration-variable derivative used in the moment recurrence. -/
theorem hasDerivAt_gaussianLaplaceKernel_variable (β x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianLaplaceKernel (β + 1) x)
      (β * gaussianLaplaceKernel β x t - gaussianLaplaceKernel (β + 1 + 1) x t +
        sqrt 2 * x * gaussianLaplaceKernel (β + 1) x t) t := by
  have h := (hasDerivAt_rpow_const (x := t) (p := β) (Or.inl ht.ne')).mul
    (((((hasDerivAt_id t).pow 2).neg.div_const 2).add
      ((hasDerivAt_id t).const_mul (sqrt 2 * x))).exp)
  convert h using 1
  · funext y
    simp only [gaussianLaplaceKernel, add_sub_cancel_right, Pi.mul_apply, Pi.add_apply,
      Pi.pow_apply, Pi.neg_apply, id_eq]
  · simp only [gaussianLaplaceKernel, add_sub_cancel_right, rpow_add_one ht.ne' β,
      Pi.add_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
    ring

/-- Integration by parts on the genuine half-line. Both endpoint terms
vanish: at zero by `β > 0`, at infinity because the function and its
explicit derivative are integrable. -/
theorem gaussianLaplaceMoment_recurrence {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    gaussianLaplaceMoment (β + 1 + 1) x =
      β * gaussianLaplaceMoment β x + sqrt 2 * x * gaussianLaplaceMoment (β + 1) x := by
  have hβ1 : 0 < β + 1 := by linarith
  have hβ2 : 0 < β + 1 + 1 := by linarith
  have h0 := integrableOn_gaussianLaplaceKernel hβ x
  have h1 := integrableOn_gaussianLaplaceKernel hβ1 x
  have h2 := integrableOn_gaussianLaplaceKernel hβ2 x
  have hD := ((h0.const_mul β).sub h2).add (h1.const_mul (sqrt 2 * x))
  have hd := fun t (ht : t ∈ Ioi (0 : ℝ)) =>
    hasDerivAt_gaussianLaplaceKernel_variable β x ht
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := gaussianLaplaceKernel (β + 1) x)
    (f' := fun t => β * gaussianLaplaceKernel β x t -
      gaussianLaplaceKernel (β + 1 + 1) x t +
        sqrt 2 * x * gaussianLaplaceKernel (β + 1) x t)
    (a := 0) (m := 0) ?_ hd hD
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd hD h1)
  · have hz : gaussianLaplaceKernel (β + 1) x 0 = 0 := by
      simp [gaussianLaplaceKernel, hβ.ne']
    rw [hz, sub_self, integral_add
      (f := fun t => β * gaussianLaplaceKernel β x t - gaussianLaplaceKernel (β + 1 + 1) x t)
      (g := fun t => sqrt 2 * x * gaussianLaplaceKernel (β + 1) x t)
      ((h0.const_mul β).sub h2) (h1.const_mul (sqrt 2 * x)),
      integral_sub (f := fun t => β * gaussianLaplaceKernel β x t)
        (g := gaussianLaplaceKernel (β + 1 + 1) x) (h0.const_mul β) h2,
      integral_const_mul, integral_const_mul] at hi
    change β * gaussianLaplaceMoment β x - gaussianLaplaceMoment (β + 1 + 1) x +
      sqrt 2 * x * gaussianLaplaceMoment (β + 1) x = 0 at hi
    linarith
  · apply Continuous.continuousWithinAt
    change Continuous (fun t : ℝ => t ^ (β + 1 - 1) * exp (-t ^ 2 / 2 + sqrt 2 * x * t))
    simp only [add_sub_cancel_right]
    exact (continuous_rpow_const hβ.le).mul
      ((((continuous_id.pow 2).neg.div_const 2).add
        (continuous_const.mul continuous_id)).rexp)

end ContinuousFlexibility.Radial
