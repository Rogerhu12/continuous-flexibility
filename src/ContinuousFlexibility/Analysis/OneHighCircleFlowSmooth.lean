module

public import ContinuousFlexibility.Analysis.OneHighCircleFlowVariational
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Joint smoothness of an actual global scalar flow

Continuity and the genuine time ODE suffice: the initial-angle derivative
is obtained from exact trajectory differences, and the two actual partial
derivatives bootstrap joint finite-order regularity. This is used after a
smooth time change of a supplied compact-interval flow; no global flow
existence or extension is assumed in that application.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The scalar integrating factor with arbitrary endpoint orientation. -/
theorem scalar_linearODE_eq_mul_exp_global {κ y : ℝ → ℝ}
    (hκ : Continuous κ) (hy : Continuous y)
    (hdy : ∀ r : ℝ, HasDerivAt y (κ r * y r) r) (a b : ℝ) :
    y b = y a * Real.exp (∫ r in a..b, κ r) := by
  rcases le_total a b with hab | hba
  · exact scalar_linearODE_eq_mul_exp hab hκ.continuousOn hy.continuousOn (fun r _ => hdy r)
  · have he := scalar_linearODE_eq_mul_exp hba hκ.continuousOn hy.continuousOn
      (fun r _ => hdy r)
    have hexp : Real.exp (∫ r in b..a, κ r) * Real.exp (∫ r in a..b, κ r) = 1 := by
      rw [intervalIntegral.integral_symm a b, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      y b = (y b * Real.exp (∫ r in b..a, κ r)) * Real.exp (∫ r in a..b, κ r) := by
        rw [mul_assoc, hexp, mul_one]
      _ = y a * Real.exp (∫ r in a..b, κ r) := by rw [← he]

/-- A continuous secant factor determines the actual derivative. -/
theorem hasDerivAt_of_continuous_secant_factor {f H : ℝ → ℝ} {θ : ℝ}
    (hH : ContinuousAt H θ) (hfactor : ∀ η : ℝ, f η - f θ = (η - θ) * H η) :
    HasDerivAt f (H θ) θ := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have he : slope f θ =ᶠ[𝓝[≠] θ] H := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [slope_def_field, hfactor η]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hη)
  exact (tendsto_congr' he).mpr (hH.tendsto.mono_left nhdsWithin_le_nhds)

/-- Initial-angle differentiability for a continuous flow defined for all
real times, obtained directly from the time equation. -/
theorem globalCircleFlow_hasDerivAt_angle {G Θ : PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ θ : ℝ, Θ (0, θ) = θ)
    (hflow : ∀ t θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) (t θ : ℝ) :
    HasDerivAt (fun η => Θ (t, η))
      (Real.exp (∫ r in (0 : ℝ)..t, angularPartial G (r, Θ (r, θ)))) θ := by
  let K : ℝ × ℝ → ℝ := fun p =>
    circleSpeedSecant G (p.2, (Θ (p.2, θ), Θ (p.2, p.1)))
  have hK : Continuous K :=
    (contDiff_circleSpeedSecant hG).continuous.comp
      (continuous_snd.prodMk
        ((hΘ.comp (continuous_snd.prodMk continuous_const)).prodMk
          (hΘ.comp (continuous_snd.prodMk continuous_fst))))
  have hfactor (η : ℝ) : Θ (t, η) - Θ (t, θ) =
      (η - θ) * Real.exp (∫ r in (0 : ℝ)..t, K (η, r)) := by
    have hκ : Continuous (fun r => K (η, r)) :=
      hK.comp (continuous_const.prodMk continuous_id)
    have hy : Continuous (fun r => Θ (r, η) - Θ (r, θ)) :=
      (hΘ.comp (continuous_id.prodMk continuous_const)).sub
        (hΘ.comp (continuous_id.prodMk continuous_const))
    have hd (r : ℝ) : HasDerivAt (fun r => Θ (r, η) - Θ (r, θ))
        (K (η, r) * (Θ (r, η) - Θ (r, θ))) r :=
      ((hflow r η).sub (hflow r θ)).congr_deriv
        (circleSpeed_sub_eq_secant hG r (Θ (r, θ)) (Θ (r, η)))
    simpa only [hinit] using scalar_linearODE_eq_mul_exp_global hκ hy hd 0 t
  have hc : Continuous (fun η => Real.exp (∫ r in (0 : ℝ)..t, K (η, r))) :=
    Real.continuous_exp.comp (continuous_parametric_intervalIntegral hK 0 t)
  have hd := hasDerivAt_of_continuous_secant_factor hc.continuousAt hfactor
  simpa only [K, circleSpeedSecant_diagonal] using hd

/-- Continuous coordinate derivatives of order `n` give genuine joint
regularity of order `n + 1`. -/
theorem contDiff_succ_of_coordinate_hasDerivAt {f A B : PolarPoint → ℝ} {n : ℕ}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B)
    (htime : ∀ t θ : ℝ, HasDerivAt (fun r => f (r, θ)) (A (t, θ)) t)
    (hangle : ∀ t θ : ℝ, HasDerivAt (fun η => f (t, η)) (B (t, θ)) θ) :
    ContDiff ℝ (n + 1) f := by
  let D : PolarPoint → PolarPoint →L[ℝ] ℝ := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ (A p)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (B p))
  have hAc : ContDiff ℝ n (fun p => ContinuousLinearMap.toSpanSingleton ℝ (A p)) := by
    apply contDiff_clm_apply_iff.mpr
    intro r
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      (contDiff_const.mul hA : ContDiff ℝ n (fun p => r * A p))
  have hBc : ContDiff ℝ n (fun p => ContinuousLinearMap.toSpanSingleton ℝ (B p)) := by
    apply contDiff_clm_apply_iff.mpr
    intro r
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      (contDiff_const.mul hB : ContDiff ℝ n (fun p => r * B p))
  have hD : ContDiff ℝ n D := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    simpa only [D, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      ((contDiff_const.mul hA).add (contDiff_const.mul hB) :
        ContDiff ℝ n (fun p => v.1 * A p + v.2 * B p))
  refine contDiff_succ_iff_hasFDerivAt.mpr ⟨D, hD, ?_⟩
  intro p
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun t θ : ℝ => f (t, θ))
    (f₁ := fun t θ => ContinuousLinearMap.toSpanSingleton ℝ (A (t, θ)))
    (f₂ := fun t θ => ContinuousLinearMap.toSpanSingleton ℝ (B (t, θ)))
    (Eventually.of_forall (fun q => (htime q.1 q.2).hasFDerivAt))
    (Eventually.of_forall (fun q => (hangle q.1 q.2).hasFDerivAt))
    hAc.continuous.continuousAt hBc.continuous.continuousAt).hasFDerivAt

/-- A continuous global classical flow of a smooth scalar speed is
jointly smooth. This theorem constructs, rather than assumes, its full
real Fréchet regularity. -/
theorem contDiff_globalCircleFlow {G Θ : PolarPoint → ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ θ : ℝ, Θ (0, θ) = θ)
    (hflow : ∀ t θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t) :
    ContDiff ℝ ∞ Θ := by
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hΘ
  | succ n ih =>
    have hA : ContDiff ℝ n (fun p : PolarPoint => G (p.1, Θ p)) :=
      (contDiff_infty.mp hG n).comp (contDiff_fst.prodMk ih)
    have hC : ContDiff ℝ n (fun p : PolarPoint => angularPartial G (p.2, Θ (p.2, p.1))) :=
      (contDiff_infty.mp (contDiff_cylinder_angularPartial hG) n).comp
        (contDiff_snd.prodMk (ih.comp (contDiff_snd.prodMk contDiff_fst)))
    have hI := contDiff_parametric_primitive_nat hC (0 : ℝ)
    have hB : ContDiff ℝ n (fun p : PolarPoint =>
        Real.exp (∫ r in (0 : ℝ)..p.1, angularPartial G (r, Θ (r, p.2)))) :=
      Real.contDiff_exp.comp (hI.comp (contDiff_snd.prodMk contDiff_fst))
    exact contDiff_succ_of_coordinate_hasDerivAt hA hB hflow
      (globalCircleFlow_hasDerivAt_angle hG hΘ hinit hflow)

end ContinuousFlexibility.Analysis
