module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Ring

/-!
# The integrating factor for a forced scalar linear equation

An actual solution of u' = κ u + f satisfies the variation-of-constants
formula. Only continuity on the closed interval and the equation on its
interior are used for the solution. The unordered interval in the
hypotheses treats both time orientations in one theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

/-- The variable-coefficient integrating-factor formula on an arbitrary
oriented compact interval. -/
theorem scalar_forced_linearODE_eq {κ f u : ℝ → ℝ} {a b : ℝ}
    (hκ : Continuous κ) (hf : Continuous f)
    (hu : ContinuousOn u (uIcc a b))
    (hdu : ∀ t ∈ uIoo a b, HasDerivAt u (κ t * u t + f t) t) :
    u b = Real.exp (∫ t in a..b, κ t) *
      (u a + ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * f t) := by
  let A : ℝ → ℝ := fun t => ∫ r in a..t, κ r
  have hA (t : ℝ) : HasDerivAt A (κ t) t :=
    (hκ.integral_hasStrictDerivAt a t).hasDerivAt
  have hAc : Continuous A :=
    continuous_iff_continuousAt.mpr (fun t => (hA t).continuousAt)
  have hEc : Continuous (fun t => Real.exp (-A t)) :=
    Real.continuous_exp.comp hAc.neg
  have hfactor_cont :
      ContinuousOn (fun t => u t * Real.exp (-A t)) (uIcc a b) :=
    hu.mul hEc.continuousOn
  have hfactor_deriv (t : ℝ) (ht : t ∈ uIoo a b) :
      HasDerivAt (fun t => u t * Real.exp (-A t))
        (Real.exp (-A t) * f t) t := by
    apply ((hdu t ht).mul (hA t).neg.exp).congr_deriv
    simp only [Pi.neg_apply]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    hfactor_cont (fun t ht => (hfactor_deriv t ht).hasDerivWithinAt)
    ((hEc.mul hf).intervalIntegrable a b)
  have hstart : A a = 0 := by
    dsimp only [A]
    exact intervalIntegral.integral_same
  rw [hstart, neg_zero, Real.exp_zero, mul_one] at hFTC
  have he : u b * Real.exp (-A b) =
      u a + ∫ t in a..b, Real.exp (-A t) * f t :=
    (sub_eq_iff_eq_add.mp hFTC.symm).trans (add_comm _ _)
  have hcancel : Real.exp (A b) * Real.exp (-A b) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    u b = u b * 1 := (mul_one _).symm
    _ = u b * (Real.exp (A b) * Real.exp (-A b)) := by rw [hcancel]
    _ = Real.exp (A b) * (u b * Real.exp (-A b)) := by ring
    _ = Real.exp (A b) * (u a + ∫ t in a..b, Real.exp (-A t) * f t) := by rw [he]
    _ = _ := rfl

/-- Zero initial data gives the forcing integral, with no restriction
on the direction from the initial point to the final point. -/
theorem scalar_forced_linearODE_zero_initial {κ f u : ℝ → ℝ} {a b : ℝ}
    (hκ : Continuous κ) (hf : Continuous f)
    (hu : ContinuousOn u (uIcc a b))
    (hdu : ∀ t ∈ uIoo a b, HasDerivAt u (κ t * u t + f t) t)
    (hzero : u a = 0) :
    u b = Real.exp (∫ t in a..b, κ t) *
      ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * f t := by
  simpa only [hzero, zero_add] using scalar_forced_linearODE_eq hκ hf hu hdu

/-- The same formula requires continuity of the coefficients only on the
actual compact time interval. A continuous clamping extension is used
solely to apply the preceding primitive calculation. -/
theorem scalar_forced_linearODE_eq_on {κ f u : ℝ → ℝ} {a b : ℝ}
    (hκ : ContinuousOn κ (uIcc a b)) (hf : ContinuousOn f (uIcc a b))
    (hu : ContinuousOn u (uIcc a b))
    (hdu : ∀ t ∈ uIoo a b, HasDerivAt u (κ t * u t + f t) t) :
    u b = Real.exp (∫ t in a..b, κ t) *
      (u a + ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * f t) := by
  let clamp : ℝ → ℝ := fun t => max (min a b) (min t (max a b))
  have hc : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  have hmem (t : ℝ) : clamp t ∈ uIcc a b :=
    ⟨le_max_left _ _, max_le min_le_max (min_le_right _ _)⟩
  have heq (t : ℝ) (ht : t ∈ uIcc a b) : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hκc : Continuous (fun t => κ (clamp t)) :=
    hκ.comp_continuous hc hmem
  have hfc : Continuous (fun t => f (clamp t)) :=
    hf.comp_continuous hc hmem
  have hduc : ∀ t ∈ uIoo a b,
      HasDerivAt u (κ (clamp t) * u t + f (clamp t)) t := by
    intro t ht
    simpa only [heq t (uIoo_subset_uIcc_self ht)] using hdu t ht
  have hsol := scalar_forced_linearODE_eq hκc hfc hu hduc
  have hI (t : ℝ) (ht : t ∈ uIcc a b) :
      (∫ r in a..t, κ (clamp r)) = ∫ r in a..t, κ r := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact congrArg κ (heq r (uIcc_subset_uIcc_left ht hr))
  have hJ :
      (∫ t in a..b, Real.exp (-(∫ r in a..t, κ (clamp r))) * f (clamp t)) =
        ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact congrArg₂ (fun x y : ℝ => Real.exp (-x) * y)
      (hI t ht) (congrArg f (heq t ht))
  rw [hI b right_mem_uIcc, hJ] at hsol
  exact hsol

/-- Compact-interval coefficients and zero initial data give the exact
forcing integral in either time orientation. -/
theorem scalar_forced_linearODE_zero_initial_on {κ f u : ℝ → ℝ} {a b : ℝ}
    (hκ : ContinuousOn κ (uIcc a b)) (hf : ContinuousOn f (uIcc a b))
    (hu : ContinuousOn u (uIcc a b))
    (hdu : ∀ t ∈ uIoo a b, HasDerivAt u (κ t * u t + f t) t)
    (hzero : u a = 0) :
    u b = Real.exp (∫ t in a..b, κ t) *
      ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) * f t := by
  simpa only [hzero, zero_add] using scalar_forced_linearODE_eq_on hκ hf hu hdu

end ContinuousFlexibility.Analysis
