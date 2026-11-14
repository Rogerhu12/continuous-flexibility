module

public import ContinuousFlexibility.Analysis.CylinderSobolev
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Integrating factors and the actual angular derivative of a circle flow

These are intermediate, norm-independent parts of the circle-flow lemma.
The smooth-flow lemmas assume joint smoothness only to establish the
variational equation from the genuine time ODE.  No angular derivative or
variational equation is supplied as independent data.  There is no choice
of angular period in this module.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The scalar integrating-factor formula needs differentiability only in
the open interval and continuity at its endpoints. -/
theorem scalar_linearODE_eq_mul_exp {κ y : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hκ : ContinuousOn κ (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hdy : ∀ t ∈ Ioo a b, HasDerivAt y (κ t * y t) t) :
    y b = y a * Real.exp (∫ t in a..b, κ t) := by
  let K : ℝ → ℝ := fun t => κ (max a (min t b))
  have hK : Continuous K :=
    hκ.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun t => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hKeq (t : ℝ) (ht : t ∈ Icc a b) : K t = κ t := by
    dsimp only [K]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hprimitive (t : ℝ) :
      HasDerivAt (fun x => ∫ r in a..x, K r) (K t) t :=
    (hK.integral_hasStrictDerivAt a t).hasDerivAt
  have hprimitive_cont : Continuous (fun x => ∫ r in a..x, K r) :=
    continuous_iff_continuousAt.mpr (fun t => (hprimitive t).continuousAt)
  have hfactor_cont :
      ContinuousOn (fun t => y t * Real.exp (-∫ r in a..t, K r)) (Icc a b) :=
    hy.mul (Real.continuous_exp.comp hprimitive_cont.neg).continuousOn
  have hfactor_deriv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun t => y t * Real.exp (-∫ r in a..t, K r)) 0 t := by
    have hd := (hdy t ht).mul (hprimitive t).neg.exp
    apply hd.congr_deriv
    rw [hKeq t (Ioo_subset_Icc_self ht)]
    ring
  have hconstant := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hfactor_cont hfactor_deriv (intervalIntegrable_const (c := (0 : ℝ)))
  have he : y b * Real.exp (-∫ r in a..b, K r) = y a := by
    simp only [intervalIntegral.integral_zero, intervalIntegral.integral_same,
      neg_zero, Real.exp_zero, mul_one] at hconstant
    linarith
  have hint : (∫ r in a..b, K r) = ∫ r in a..b, κ r := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact hKeq r (by simpa only [uIcc_of_le hab] using hr)
  calc
    y b = (y b * Real.exp (-∫ r in a..b, K r)) *
        Real.exp (∫ r in a..b, K r) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = y a * Real.exp (∫ r in a..b, K r) := by rw [he]
    _ = y a * Real.exp (∫ r in a..b, κ r) := by rw [hint]

/-- Commuting actual partial derivatives of a smooth solution derives the
angular variational equation directly from its time ODE. -/
theorem smoothCircleFlow_angular_variational {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Ioo a b) (θ : ℝ) :
    HasDerivAt (fun r => angularPartial Θ (r, θ))
      (angularPartial G (t, Θ (t, θ)) * angularPartial Θ (t, θ)) t := by
  have hΘr := contDiff_cylinder_radialPartial hΘ
  have hΘθ := contDiff_cylinder_angularPartial hΘ
  have heq : (fun η => radialPartial Θ (t, η)) =
      fun η => G (t, Θ (t, η)) := by
    funext η
    exact (deriv_cylinder_radial_slice (hΘ.differentiable (by simp)) t η).symm.trans
      (hflow t ht η).deriv
  have hangle (r η : ℝ) : HasDerivAt (fun x => Θ (r, x))
      (angularPartial Θ (r, η)) η :=
    ((hΘ.differentiable (by simp) (r, η)).hasFDerivAt.comp_hasDerivAt η
      ((hasDerivAt_const η r).prodMk (hasDerivAt_id η)))
  have hGangle (r η : ℝ) : HasDerivAt (fun x => G (r, x))
      (angularPartial G (r, η)) η :=
    ((hG.differentiable (by simp) (r, η)).hasFDerivAt.comp_hasDerivAt η
      ((hasDerivAt_const η r).prodMk (hasDerivAt_id η)))
  have hd := ((hΘθ.differentiable (by simp) (t, θ)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t θ)))
  apply hd.congr_deriv
  calc
    radialPartial (angularPartial Θ) (t, θ) =
        angularPartial (radialPartial Θ) (t, θ) :=
      radial_angular_commute (hΘ.contDiffAt.of_le (by simp))
    _ = deriv (fun η => radialPartial Θ (t, η)) θ :=
      (deriv_cylinder_angular_slice (hΘr.differentiable (by simp)) t θ).symm
    _ = deriv (fun η => G (t, Θ (t, η))) θ := by rw [heq]
    _ = angularPartial G (t, Θ (t, θ)) * angularPartial Θ (t, θ) := by
      have hcomp : HasDerivAt (fun η : ℝ => G (t, Θ (t, η)))
          (angularPartial G (t, Θ (t, θ)) * angularPartial Θ (t, θ)) θ :=
        HasDerivAt.comp (𝕜 := ℝ) (𝕜' := ℝ)
          (h := fun η : ℝ => Θ (t, η)) (h₂ := fun η : ℝ => G (t, η))
          (h' := angularPartial Θ (t, θ)) (h₂' := angularPartial G (t, Θ (t, θ)))
          θ (hGangle t (Θ (t, θ))) (hangle t θ)
      exact hcomp.deriv

/-- The actual angular Jacobian of a smooth flow is the exponential of
the integrated angular derivative of its speed. -/
theorem smoothCircleFlow_angular_eq_exp {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ)
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    angularPartial Θ (t, θ) =
      Real.exp (∫ r in a..t, angularPartial G (r, Θ (r, θ))) := by
  have hΘθ := contDiff_cylinder_angularPartial hΘ
  have hGθ := contDiff_cylinder_angularPartial hG
  have hκ : Continuous (fun r => angularPartial G (r, Θ (r, θ))) :=
    hGθ.continuous.comp
      (continuous_id.prodMk (hΘ.continuous.comp (continuous_id.prodMk continuous_const)))
  have hy : Continuous (fun r => angularPartial Θ (r, θ)) :=
    hΘθ.continuous.comp (continuous_id.prodMk continuous_const)
  have hy0 : angularPartial Θ (a, θ) = 1 := by
    rw [← deriv_cylinder_angular_slice (hΘ.differentiable (by simp)) a θ,
      show (fun η => Θ (a, η)) = (fun η : ℝ => η) from funext hinit]
    exact (hasDerivAt_id θ).deriv
  have he := scalar_linearODE_eq_mul_exp ht.1 hκ.continuousOn hy.continuousOn
    (fun r hr => smoothCircleFlow_angular_variational hG hΘ hflow
      ⟨hr.1, hr.2.trans_le ht.2⟩ θ)
  simpa only [hy0, one_mul] using he

theorem smoothCircleFlow_deriv_eq_exp {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ)
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    deriv (fun η => Θ (t, η)) θ =
      Real.exp (∫ r in a..t, deriv (fun η => G (r, η)) (Θ (r, θ))) := by
  simpa only [deriv_cylinder_angular_slice (hΘ.differentiable (by simp)),
    deriv_cylinder_angular_slice (hG.differentiable (by simp))] using
    smoothCircleFlow_angular_eq_exp hG hΘ hinit hflow ht θ

theorem smoothCircleFlow_angular_pos {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ)
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) : 0 < angularPartial Θ (t, θ) := by
  rw [smoothCircleFlow_angular_eq_exp hG hΘ hinit hflow ht θ]
  exact Real.exp_pos _

/-- A time-dependent pointwise envelope yields the uniform two-sided
Jacobian bound; a circle Sobolev embedding can supply this envelope. -/
theorem smoothCircleFlow_angular_bounds {G Θ : PolarPoint → ℝ} {a b : ℝ}
    (hG : ContDiff ℝ ∞ G) (hΘ : ContDiff ℝ ∞ Θ)
    (hinit : ∀ θ : ℝ, Θ (a, θ) = θ)
    (hflow : ∀ t ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun r => Θ (r, θ)) (G (t, Θ (t, θ))) t)
    {B : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ r ∈ Icc a b, ∀ η : ℝ, |angularPartial G (r, η)| ≤ B r)
    {t : ℝ} (ht : t ∈ Icc a b) (θ : ℝ) :
    Real.exp (-(∫ r in a..b, B r)) ≤ angularPartial Θ (t, θ) ∧
      angularPartial Θ (t, θ) ≤ Real.exp (∫ r in a..b, B r) := by
  have hBat : IntervalIntegrable B volume a t :=
    (hB.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hBtb : IntervalIntegrable B volume t b :=
    (hB.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  have hκ : Continuous (fun r => angularPartial G (r, Θ (r, θ))) :=
    (contDiff_cylinder_angularPartial hG).continuous.comp
      (continuous_id.prodMk (hΘ.continuous.comp (continuous_id.prodMk continuous_const)))
  have hmono : (∫ r in a..t, |angularPartial G (r, Θ (r, θ))|) ≤
      ∫ r in a..t, B r :=
    intervalIntegral.integral_mono_on ht.1 (hκ.abs.intervalIntegrable a t) hBat
      (fun r hr => hbound r ⟨hr.1, hr.2.trans ht.2⟩ _)
  have htail : 0 ≤ ∫ r in t..b, B r :=
    intervalIntegral.integral_nonneg ht.2
      (fun r hr => (abs_nonneg (angularPartial G (r, 0))).trans
        (hbound r ⟨ht.1.trans hr.1, hr.2⟩ 0))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hBat hBtb
  have htotal : |∫ r in a..t, angularPartial G (r, Θ (r, θ))| ≤
      ∫ r in a..b, B r := by
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun r => angularPartial G (r, Θ (r, θ))) ht.1
    linarith
  rw [smoothCircleFlow_angular_eq_exp hG hΘ hinit hflow ht θ]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp htotal).1,
    Real.exp_le_exp.mpr (abs_le.mp htotal).2⟩

end ContinuousFlexibility.Analysis
