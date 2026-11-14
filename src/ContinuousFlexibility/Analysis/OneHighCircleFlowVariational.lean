module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowBasic
public import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Initial-angle differentiability from the genuine flow equation

The finite difference of two classical time solutions satisfies an exact
scalar linear equation. Its coefficient is the integral of the actual
angular derivative of the speed along the segment joining the solutions.
The initial-angle derivative follows by taking a difference-quotient
limit, without assuming any angular differentiability of the flow.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- The continuous divided difference of the speed, including its value
on the diagonal. Its entries are time, first angle, and second angle. -/
def circleSpeedSecant (G : PolarPoint → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  ∫ s in (0 : ℝ)..1, angularPartial G (p.1, (p.2.2 - p.2.1) * s + p.2.1)

theorem contDiff_circleSpeedSecant {G : PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (circleSpeedSecant G) := by
  have hc : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
      angularPartial G (q.1.1, (q.1.2.2 - q.1.2.1) * q.2 + q.1.2.1)) :=
    (contDiff_cylinder_angularPartial hG).comp
      (contDiff_fst.fst.prodMk
        (((contDiff_fst.snd.snd.sub contDiff_fst.snd.fst).mul contDiff_snd).add
          contDiff_fst.snd.fst))
  exact contDiff_parametric_intervalIntegral hc 0 1

theorem circleSpeedSecant_diagonal (G : PolarPoint → ℝ) (t x : ℝ) :
    circleSpeedSecant G (t, (x, x)) = angularPartial G (t, x) := by
  simp only [circleSpeedSecant, sub_self, zero_mul, zero_add,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem circleSpeed_sub_eq_secant {G : PolarPoint → ℝ} (hG : ContDiff ℝ ∞ G)
    (t x y : ℝ) :
    G (t, y) - G (t, x) = circleSpeedSecant G (t, (x, y)) * (y - x) := by
  have hd (r : ℝ) : HasDerivAt (fun η => G (t, η)) (angularPartial G (t, r)) r :=
    (hG.differentiable (by simp) (t, r)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r t).prodMk (hasDerivAt_id r))
  have hc : Continuous (fun r => angularPartial G (t, r)) :=
    (contDiff_cylinder_angularPartial hG).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hint : (∫ r in x..y, angularPartial G (t, r)) = G (t, y) - G (t, x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
      (hc.intervalIntegrable x y)
  have hscale := intervalIntegral.smul_integral_comp_mul_add
    (fun r => angularPartial G (t, r)) (a := (0 : ℝ)) (b := 1) (y - x) x
  calc
    G (t, y) - G (t, x) = ∫ r in x..y, angularPartial G (t, r) := hint.symm
    _ = (y - x) * circleSpeedSecant G (t, (x, y)) := by
      simpa only [circleSpeedSecant, smul_eq_mul, mul_zero, zero_add, mul_one,
        sub_add_cancel] using hscale.symm
    _ = circleSpeedSecant G (t, (x, y)) * (y - x) := mul_comm _ _

/-- Exact differences of two classical trajectories satisfy a scalar
linear equation, without any parameter regularity hypothesis. -/
theorem circleTrajectory_difference_eq_mul_exp {G : PolarPoint → ℝ} {u v : ℝ → ℝ}
    {a b : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (G (t, u t)) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivAt v (G (t, v t)) t) :
    u b - v b = (u a - v a) *
      Real.exp (∫ r in a..b, circleSpeedSecant G (r, (v r, u r))) := by
  have hκ : ContinuousOn
      (fun r => circleSpeedSecant G (r, (v r, u r))) (Icc a b) :=
    (contDiff_circleSpeedSecant hG).continuous.comp_continuousOn
      (continuousOn_id.prodMk (hv.prodMk hu))
  apply scalar_linearODE_eq_mul_exp hab hκ (hu.sub hv)
  intro r hr
  exact ((hdu r hr).sub (hdv r hr)).congr_deriv
    (circleSpeed_sub_eq_secant hG r (v r) (u r))

/-- The same exact formula for two initial angles of a family. -/
theorem circleFlow_difference_eq_mul_exp {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hG : ContDiff ℝ ∞ G)
    (hΘ : ∀ θ : ℝ, ContinuousOn (fun r => Θ (r, θ)) (Icc a b))
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) (η θ : ℝ) :
    Θ (b, η) - Θ (b, θ) = (Θ (a, η) - Θ (a, θ)) *
      Real.exp (∫ r in a..b, circleSpeedSecant G (r, (Θ (r, θ), Θ (r, η)))) :=
  circleTrajectory_difference_eq_mul_exp hab hG (hΘ η) (hΘ θ)
    (fun r hr => hflow r hr η) (fun r hr => hflow r hr θ)

/-- A jointly continuous classical flow has the actual initial-angle
derivative given by the variational exponential. The proof obtains this
derivative as a limit of the exact finite-difference formula. -/
theorem continuousCircleFlow_hasDerivAt_angle {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContinuousOn Θ (Icc a b ×ˢ (univ : Set ℝ)))
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => Θ (t, η))
      (Real.exp (∫ r in a..t, angularPartial G (r, Θ (r, θ)))) θ := by
  let clamp : ℝ → ℝ := fun r => max a (min r b)
  have hclamp : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  have hclamp_mem (r : ℝ) : clamp r ∈ Icc a b :=
    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_right _ _)⟩
  have hclamp_eq (r : ℝ) (hr : r ∈ Icc a b) : clamp r = r := by
    dsimp only [clamp]
    rw [min_eq_left hr.2, max_eq_right hr.1]
  have hclamped : Continuous (fun p : PolarPoint => Θ (clamp p.1, p.2)) :=
    hΘ.comp_continuous ((hclamp.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hclamp_mem p.1, mem_univ p.2⟩)
  let K : ℝ × ℝ → ℝ := fun p =>
    circleSpeedSecant G (p.2, (Θ (clamp p.2, θ), Θ (clamp p.2, p.1)))
  have hK : Continuous K :=
    (contDiff_circleSpeedSecant hG).continuous.comp
      (continuous_snd.prodMk
        ((hclamped.comp (continuous_snd.prodMk continuous_const)).prodMk
          (hclamped.comp (continuous_snd.prodMk continuous_fst))))
  have hKeq (η r : ℝ) (hr : r ∈ Icc a b) :
      K (η, r) = circleSpeedSecant G (r, (Θ (r, θ), Θ (r, η))) := by
    dsimp only [K]
    rw [hclamp_eq r hr]
  have hIK (η : ℝ) : (∫ r in a..t, K (η, r)) =
      ∫ r in a..t, circleSpeedSecant G (r, (Θ (r, θ), Θ (r, η))) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
    exact hKeq η r ⟨hr'.1, hr'.2.trans ht.2⟩
  have htime (η : ℝ) : ContinuousOn (fun r => Θ (r, η)) (Icc a t) :=
    hΘ.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨⟨hr.1, hr.2.trans ht.2⟩, mem_univ η⟩)
  have hdiff (η : ℝ) : Θ (t, η) - Θ (t, θ) =
      (η - θ) * Real.exp (∫ r in a..t, K (η, r)) := by
    rw [hIK η]
    simpa only [hinit] using circleFlow_difference_eq_mul_exp ht.1 hG htime
      (fun r hr => hflow r ⟨hr.1, hr.2.trans_le ht.2⟩) η θ
  have hdiag : (∫ r in a..t, K (θ, r)) =
      ∫ r in a..t, angularPartial G (r, Θ (r, θ)) := by
    rw [hIK θ]
    simp only [circleSpeedSecant_diagonal]
  have hcont : Continuous (fun η => Real.exp (∫ r in a..t, K (η, r))) :=
    Real.continuous_exp.comp (continuous_parametric_intervalIntegral hK a t)
  have hlim : Tendsto (fun η => Real.exp (∫ r in a..t, K (η, r))) (𝓝[≠] θ)
      (𝓝 (Real.exp (∫ r in a..t, angularPartial G (r, Θ (r, θ))))) := by
    rw [← hdiag]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope : slope (fun η => Θ (t, η)) θ =ᶠ[𝓝[≠] θ]
      (fun η => Real.exp (∫ r in a..t, K (η, r))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [slope_def_field, hdiff η]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hη)
  exact hasDerivAt_iff_tendsto_slope.mpr ((tendsto_congr' hslope).mpr hlim)

end ContinuousFlexibility.Analysis
