import ContinuousFlexibility.Analysis.ScalarForcedLinearODE
import ContinuousFlexibility.Scalar.RectangleParameterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
# Exact secant equations for two scalar trajectories

The averaged angular derivative is an actual integral of a supplied
derivative of the vector field. The fundamental theorem of calculus
converts differences of the nonlinear field into this coefficient times
the trajectory difference. Different vector fields produce a genuine
forcing term. No derivative of a trajectory in an external parameter is
assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

/-- The continuous secant coefficient associated to an actual angular
derivative. The three entries are time and the two angular values. -/
def scalarSecantAverage (D : ℝ × ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  ∫ s in (0 : ℝ)..1, D (p.1, (p.2.2 - p.2.1) * s + p.2.1)

/-- Joint continuity of the angular derivative gives joint continuity of
the secant coefficient, including on the diagonal. -/
theorem continuous_scalarSecantAverage {D : ℝ × ℝ → ℝ}
    (hD : Continuous D) : Continuous (scalarSecantAverage D) := by
  have h : Continuous (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
      D (q.1.1, (q.1.2.2 - q.1.2.1) * q.2 + q.1.2.1)) :=
    hD.comp (continuous_fst.fst.prodMk
      (((continuous_fst.snd.snd.sub continuous_fst.snd.fst).mul continuous_snd).add
        continuous_fst.snd.fst))
  have hc : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      ∫ s in Icc (0 : ℝ) 1, D (p.1, (p.2.2 - p.2.1) * s + p.2.1)) :=
    continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun (p : ℝ × (ℝ × ℝ)) (s : ℝ) =>
        D (p.1, (p.2.2 - p.2.1) * s + p.2.1))
      h isCompact_Icc
  have he : scalarSecantAverage D = fun p : ℝ × (ℝ × ℝ) =>
      ∫ s in Icc (0 : ℝ) 1, D (p.1, (p.2.2 - p.2.1) * s + p.2.1) := by
    funext p
    dsimp only [scalarSecantAverage]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rw [he]
  exact hc

theorem scalarSecantAverage_diagonal (D : ℝ × ℝ → ℝ) (t x : ℝ) :
    scalarSecantAverage D (t, (x, x)) = D (t, x) := by
  simp only [scalarSecantAverage, sub_self, zero_mul, zero_add,
    intervalIntegral.integral_const, sub_zero, one_smul]

/-- The secant identity uses the derivative of the actual field, including
the case of coincident trajectory values. -/
theorem scalarField_sub_eq_secant {F D : ℝ × ℝ → ℝ}
    (hD : Continuous D)
    (hderiv : ∀ t x : ℝ, HasDerivAt (fun y => F (t, y)) (D (t, x)) x)
    (t x y : ℝ) :
    F (t, y) - F (t, x) = scalarSecantAverage D (t, (x, y)) * (y - x) := by
  have hc : Continuous (fun r => D (t, r)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  have hint : (∫ r in x..y, D (t, r)) = F (t, y) - F (t, x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hderiv t r) (hc.intervalIntegrable x y)
  have hscale := intervalIntegral.smul_integral_comp_mul_add
    (fun r => D (t, r)) (a := (0 : ℝ)) (b := 1) (y - x) x
  calc
    F (t, y) - F (t, x) = ∫ r in x..y, D (t, r) := hint.symm
    _ = (y - x) * scalarSecantAverage D (t, (x, y)) := by
      simpa only [scalarSecantAverage, smul_eq_mul, mul_zero, zero_add, mul_one,
        sub_add_cancel] using hscale.symm
    _ = scalarSecantAverage D (t, (x, y)) * (y - x) := mul_comm _ _

/-- Two actual trajectories for possibly different fields satisfy the
inhomogeneous secant equation at every time where both equations hold. -/
theorem scalarTrajectory_difference_hasDerivAt
    {F₁ F₀ D₁ : ℝ × ℝ → ℝ} {u₁ u₀ : ℝ → ℝ} {t : ℝ}
    (hD₁ : Continuous D₁)
    (hderiv : ∀ t x : ℝ, HasDerivAt (fun y => F₁ (t, y)) (D₁ (t, x)) x)
    (hu₁ : HasDerivAt u₁ (F₁ (t, u₁ t)) t)
    (hu₀ : HasDerivAt u₀ (F₀ (t, u₀ t)) t) :
    HasDerivAt (fun r => u₁ r - u₀ r)
      (scalarSecantAverage D₁ (t, (u₀ t, u₁ t)) * (u₁ t - u₀ t) +
        (F₁ (t, u₀ t) - F₀ (t, u₀ t))) t := by
  apply (hu₁.sub hu₀).congr_deriv
  rw [← scalarField_sub_eq_secant hD₁ hderiv t (u₀ t) (u₁ t)]
  ring

/-- The coefficient along two continuous trajectories remains continuous
on their actual time domain. -/
theorem continuousOn_scalarTrajectory_secant
    {D : ℝ × ℝ → ℝ} {u₁ u₀ : ℝ → ℝ} {I : Set ℝ}
    (hD : Continuous D) (hu₁ : ContinuousOn u₁ I) (hu₀ : ContinuousOn u₀ I) :
    ContinuousOn (fun t => scalarSecantAverage D (t, (u₀ t, u₁ t))) I :=
  (continuous_scalarSecantAverage hD).comp_continuousOn
    (continuousOn_id.prodMk (hu₀.prodMk hu₁))

/-- The forcing is the difference of the two actual vector fields,
evaluated on the reference trajectory. -/
theorem continuousOn_scalarTrajectory_forcing
    {F₁ F₀ : ℝ × ℝ → ℝ} {u₀ : ℝ → ℝ} {I : Set ℝ}
    (hF₁ : Continuous F₁) (hF₀ : Continuous F₀) (hu₀ : ContinuousOn u₀ I) :
    ContinuousOn (fun t => F₁ (t, u₀ t) - F₀ (t, u₀ t)) I :=
  (hF₁.sub hF₀).comp_continuousOn (continuousOn_id.prodMk hu₀)

/-- Exact variation of constants for two actual trajectories of
different scalar fields. Every coefficient in the integral is obtained
from the supplied vector fields and the actual trajectories. -/
theorem scalarTrajectory_difference_eq
    {F₁ F₀ D₁ : ℝ × ℝ → ℝ} {u₁ u₀ : ℝ → ℝ} {a b : ℝ}
    (hF₁ : Continuous F₁) (hF₀ : Continuous F₀) (hD₁ : Continuous D₁)
    (hderiv : ∀ t x : ℝ, HasDerivAt (fun y => F₁ (t, y)) (D₁ (t, x)) x)
    (hu₁ : ContinuousOn u₁ (uIcc a b)) (hu₀ : ContinuousOn u₀ (uIcc a b))
    (hdu₁ : ∀ t ∈ uIoo a b, HasDerivAt u₁ (F₁ (t, u₁ t)) t)
    (hdu₀ : ∀ t ∈ uIoo a b, HasDerivAt u₀ (F₀ (t, u₀ t)) t) :
    u₁ b - u₀ b =
      Real.exp (∫ t in a..b, scalarSecantAverage D₁ (t, (u₀ t, u₁ t))) *
        (u₁ a - u₀ a +
          ∫ t in a..b,
            Real.exp (-(∫ r in a..t, scalarSecantAverage D₁ (r, (u₀ r, u₁ r)))) *
              (F₁ (t, u₀ t) - F₀ (t, u₀ t))) := by
  exact scalar_forced_linearODE_eq_on
    (continuousOn_scalarTrajectory_secant hD₁ hu₁ hu₀)
    (continuousOn_scalarTrajectory_forcing hF₁ hF₀ hu₀) (hu₁.sub hu₀)
    (fun t ht => scalarTrajectory_difference_hasDerivAt hD₁ hderiv
      (hdu₁ t ht) (hdu₀ t ht))

end ContinuousFlexibility.Analysis
