import ContinuousFlexibility.Analysis.ScalarFlowParameterFDeriv

/-!
# The actual initial-angle Jacobian of a scalar flow

The parameter variational formula with identity initial value and a
parameter-independent field gives the exponential Jacobian. In
particular, the newly chosen flow has a strictly positive angular
derivative. The statement treats either order of the time endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

variable {F D : ℝ × ℝ → ℝ} {Θ : ℝ × ℝ → ℝ} {a b : ℝ}
  (hD : Continuous D)
  (hangle : ∀ t x : ℝ,
    HasDerivAt (fun y => F (t, y)) (D (t, x)) x)
  (hΘ : ContinuousOn Θ ((univ : Set ℝ) ×ˢ uIcc a b))
  (hinit : ∀ θ : ℝ, Θ (θ, a) = θ)
  (hflow : ∀ θ t : ℝ, t ∈ uIcc a b →
    HasDerivWithinAt (fun r => Θ (θ, r))
      (F (t, Θ (θ, t))) (uIcc a b) t)

/-- The angular derivative of the actual chosen flow is its exponential
variational factor; no angular differentiability of the flow is assumed. -/
theorem scalarFlow_hasDerivAt_initialAngle (θ : ℝ) :
    HasDerivAt (fun φ => Θ (φ, b))
      (Real.exp (∫ t in a..b, D (t, Θ (θ, t)))) θ := by
  have hd := scalarFlow_hasFDerivAt_parameter
    (F := fun z : ℝ × (ℝ × ℝ) => F z.2)
    (Dθ := fun z : ℝ × (ℝ × ℝ) => D z.2)
    (Dp := fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ →L[ℝ] ℝ))
    (Θ := Θ) (v := id)
    (Dv := fun _ : ℝ => ContinuousLinearMap.id ℝ ℝ) (a := a) (b := b)
    (hD.comp continuous_snd) continuous_const continuous_const
    (fun _ t x => hangle t x)
    (fun q t x => hasFDerivAt_const (c := F (t, x)) (x := q))
    (fun q => hasFDerivAt_id q) hΘ hinit
    (fun q t ht => (hflow q t (uIoo_subset_uIcc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) θ
  simpa only [smul_zero, intervalIntegral.integral_zero, add_zero,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one] using hd.hasDerivAt

/-- The true initial-angle Jacobian is strictly positive. -/
theorem scalarFlow_initialAngle_deriv_pos (θ : ℝ) :
    0 < deriv (fun φ => Θ (φ, b)) θ := by
  rw [(scalarFlow_hasDerivAt_initialAngle hD hangle hΘ hinit hflow θ).deriv]
  exact Real.exp_pos _

end ContinuousFlexibility.Analysis
