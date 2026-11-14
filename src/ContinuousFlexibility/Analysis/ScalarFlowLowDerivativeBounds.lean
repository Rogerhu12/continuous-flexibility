module

public import ContinuousFlexibility.Analysis.ScalarFlowInitialAngle
public import ContinuousFlexibility.Analysis.ScalarFlowParameterFDeriv
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum

/-!
# Actual low-order scalar flow derivative bounds

A bound on the true angular derivative of the field controls the
exponential initial-angle Jacobian. The genuine parameter variational
formula is then estimated by the interval-integral norm inequality.
The parameter bound is linear in the field's parameter derivative norm
and the initial-data derivative norm; no derivative bound for the flow
is supplied as an assumption.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

/-- A real interval integral is bounded by the actual pointwise bound
on the unordered closed interval. -/
theorem abs_intervalIntegral_le_const_of_uIcc
    {κ : ℝ → ℝ} {a b L : ℝ}
    (hκ : ∀ t ∈ uIcc a b, |κ t| ≤ L) :
    |∫ t in a..b, κ t| ≤ L * |b - a| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := κ) (a := a) (b := b) (C := L)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using hκ t (uIoc_subset_uIcc ht))
  simpa only [Real.norm_eq_abs] using h

/-- The logarithmic smallness threshold gives the exact constants
one half and two, without a numerical approximation to the exponential. -/
theorem exp_bounds_of_abs_le_log_two {x : ℝ}
    (hx : |x| ≤ Real.log 2) :
    (1 / 2 : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ 2 := by
  have hlo := Real.exp_le_exp.mpr (abs_le.mp hx).1
  have hhi := Real.exp_le_exp.mpr (abs_le.mp hx).2
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hlo
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hhi
  exact ⟨by simpa only [one_div] using hlo, hhi⟩

/-- The actual variational operator is linear in the high input norm
once the scalar angular coefficient has the fixed small integral bound. -/
theorem scalar_variationalOperator_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {κ : ℝ → ℝ} {A : ℝ → E} {v : E} {a b L M V : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hv : ‖v‖ ≤ V)
    (hκ : ∀ t ∈ uIcc a b, |κ t| ≤ L)
    (hA : ∀ t ∈ uIcc a b, ‖A t‖ ≤ M)
    (hsmall : L * |b - a| ≤ Real.log 2) :
    ‖Real.exp (∫ t in a..b, κ t) •
        (v + ∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) • A t)‖ ≤
      2 * (V + 2 * M * |b - a|) := by
  have hprefix (t : ℝ) (ht : t ∈ uIcc a b) :
      |∫ r in a..t, κ r| ≤ Real.log 2 := by
    calc
      _ ≤ L * |t - a| :=
        abs_intervalIntegral_le_const_of_uIcc
          (fun r hr => hκ r (uIcc_subset_uIcc_left ht hr))
      _ ≤ L * |b - a| :=
        mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht) hL
      _ ≤ Real.log 2 := hsmall
  have hweight (t : ℝ) (ht : t ∈ uIcc a b) :
      ‖Real.exp (-(∫ r in a..t, κ r)) • A t‖ ≤ 2 * M := by
    have he : Real.exp (-(∫ r in a..t, κ r)) ≤ 2 :=
      (exp_bounds_of_abs_le_log_two
        (x := -(∫ r in a..t, κ r))
        (by simpa only [abs_neg] using hprefix t ht)).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he (hA t ht) (norm_nonneg _) (by norm_num)
  have hI :
      ‖∫ t in a..b, Real.exp (-(∫ r in a..t, κ r)) • A t‖ ≤
        (2 * M) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => Real.exp (-(∫ r in a..t, κ r)) • A t)
      (a := a) (b := b) (C := 2 * M)
      (fun t ht => hweight t (uIoc_subset_uIcc ht))
  have he : Real.exp (∫ t in a..b, κ t) ≤ 2 :=
    (exp_bounds_of_abs_le_log_two (hprefix b right_mem_uIcc)).2
  have hV : 0 ≤ V := (norm_nonneg v).trans hv
  have hsum : 0 ≤ V + 2 * M * |b - a| :=
    add_nonneg hV (mul_nonneg (mul_nonneg (by norm_num) hM) (abs_nonneg _))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (∫ t in a..b, κ t) * (V + 2 * M * |b - a|) :=
      mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add hv hI)) (Real.exp_pos _).le
    _ ≤ 2 * (V + 2 * M * |b - a|) :=
      mul_le_mul_of_nonneg_right he hsum

/-- A genuine field angular derivative bound gives uniform endpoint
Jacobian bounds for the actual chosen flow. -/
theorem scalarFlow_initialAngle_deriv_bounds
    {F D : ℝ × ℝ → ℝ} {Θ : ℝ × ℝ → ℝ} {a b L : ℝ}
    (hD : Continuous D)
    (hangle : ∀ t x : ℝ,
      HasDerivAt (fun y => F (t, y)) (D (t, x)) x)
    (hΘ : ContinuousOn Θ ((univ : Set ℝ) ×ˢ uIcc a b))
    (hinit : ∀ θ : ℝ, Θ (θ, a) = θ)
    (hflow : ∀ θ t : ℝ, t ∈ uIcc a b →
      HasDerivWithinAt (fun r => Θ (θ, r))
        (F (t, Θ (θ, t))) (uIcc a b) t)
    (hbound : ∀ t ∈ uIcc a b, ∀ x : ℝ, |D (t, x)| ≤ L)
    (hsmall : L * |b - a| ≤ Real.log 2) (θ : ℝ) :
    (1 / 2 : ℝ) ≤ deriv (fun φ => Θ (φ, b)) θ ∧
      deriv (fun φ => Θ (φ, b)) θ ≤ 2 := by
  rw [(scalarFlow_hasDerivAt_initialAngle
    (F := F) (D := D) (Θ := Θ) hD hangle hΘ hinit hflow θ).deriv]
  exact exp_bounds_of_abs_le_log_two
    ((abs_intervalIntegral_le_const_of_uIcc
      (fun t ht => hbound t ht (Θ (θ, t)))).trans hsmall)

/-- The genuine external-parameter derivative is bounded by the true
field derivative norm and initial derivative norm. The constants are
independent of the size of the high parameter derivative norm. -/
theorem scalarFlow_parameter_fderiv_norm_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {F Dθ : P × (ℝ × ℝ) → ℝ} {Dp : P × (ℝ × ℝ) → P →L[ℝ] ℝ}
    {Θ : P × ℝ → ℝ} {v : P → ℝ} {Dv : P → P →L[ℝ] ℝ}
    {a b L M V : ℝ}
    (hDθ : Continuous Dθ) (hDp : Continuous Dp) (hDv : Continuous Dv)
    (hangle : ∀ p : P, ∀ t x : ℝ,
      HasDerivAt (fun y => F (p, (t, y))) (Dθ (p, (t, x))) x)
    (hparameter : ∀ p : P, ∀ t x : ℝ,
      HasFDerivAt (fun q => F (q, (t, x))) (Dp (p, (t, x))) p)
    (hvalue : ∀ p : P, HasFDerivAt v (Dv p) p)
    (hΘ : ContinuousOn Θ ((univ : Set P) ×ˢ uIcc a b))
    (hinit : ∀ p : P, Θ (p, a) = v p)
    (hflow : ∀ p : P, ∀ t ∈ uIoo a b,
      HasDerivAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) t)
    (p : P) (hL : 0 ≤ L) (hM : 0 ≤ M) (hv : ‖Dv p‖ ≤ V)
    (hangleBound : ∀ t ∈ uIcc a b, ∀ x : ℝ, |Dθ (p, (t, x))| ≤ L)
    (hparameterBound : ∀ t ∈ uIcc a b, ∀ x : ℝ, ‖Dp (p, (t, x))‖ ≤ M)
    (hsmall : L * |b - a| ≤ Real.log 2) :
    ‖fderiv ℝ (fun q : P => Θ (q, b)) p‖ ≤ 2 * (V + 2 * M * |b - a|) := by
  have hd := scalarFlow_hasFDerivAt_parameter
    (F := F) (Dθ := Dθ) (Dp := Dp) (Θ := Θ) (v := v) (Dv := Dv) (a := a) (b := b)
    hDθ hDp hDv hangle hparameter hvalue hΘ hinit hflow p
  rw [hd.fderiv]
  exact scalar_variationalOperator_norm_le
    (κ := fun t => Dθ (p, (t, Θ (p, t))))
    (A := fun t => Dp (p, (t, Θ (p, t)))) (v := Dv p)
    hL hM hv (fun t ht => hangleBound t ht (Θ (p, t)))
      (fun t ht => hparameterBound t ht (Θ (p, t))) hsmall

end ContinuousFlexibility.Analysis
