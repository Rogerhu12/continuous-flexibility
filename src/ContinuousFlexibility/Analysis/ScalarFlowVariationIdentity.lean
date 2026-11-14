import ContinuousFlexibility.Analysis.ScalarFlowInitialAngle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The true external-parameter variation as a Jacobian kernel

The previously derived parameter derivative and initial-angle derivative
formulas identify the actual directional parameter variation with the
forward Jacobian times the integral of its reciprocal-Jacobian kernel.
No parameter derivative of the chosen flow is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

/-- The actual external-parameter derivative, evaluated in a direction,
has the circle-flow variation-kernel representation. -/
theorem scalarFlow_parameter_fderiv_apply_eq_kernel
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F Dθ : E × (ℝ × ℝ) → ℝ} {Dp : E × (ℝ × ℝ) → E →L[ℝ] ℝ}
    {Θ : E → ℝ → ℝ → ℝ} {a b : ℝ}
    (hDθ : Continuous Dθ) (hDp : Continuous Dp)
    (hangle : ∀ p : E, ∀ t x : ℝ,
      HasDerivAt (fun y => F (p, (t, y))) (Dθ (p, (t, x))) x)
    (hparameter : ∀ p : E, ∀ t x : ℝ,
      HasFDerivAt (fun q => F (q, (t, x))) (Dp (p, (t, x))) p)
    (hΘ : ContinuousOn (fun z : (E × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2)
      (univ ×ˢ uIcc a b))
    (hinit : ∀ p θ, Θ p a θ = θ)
    (hflow : ∀ p θ t, t ∈ uIcc a b →
      HasDerivWithinAt (fun r => Θ p r θ)
        (F (p, (t, Θ p t θ))) (uIcc a b) t)
    (p e : E) (θ : ℝ) :
    fderiv ℝ (fun q : E => Θ q b θ) p e =
      deriv (fun η => Θ p b η) θ *
        ∫ t in a..b, Dp (p, (t, Θ p t θ)) e / deriv (fun η => Θ p t η) θ := by
  have hjoint : ContinuousOn (fun z : E × ℝ => Θ z.1 z.2 θ)
      (univ ×ˢ uIcc a b) :=
    hΘ.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hd := scalarFlow_hasFDerivAt_parameter
    (F := F) (Dθ := Dθ) (Dp := Dp)
    (Θ := fun z : E × ℝ => Θ z.1 z.2 θ)
    (v := fun _ : E => θ) (Dv := fun _ : E => (0 : E →L[ℝ] ℝ))
    (a := a) (b := b) hDθ hDp continuous_const hangle hparameter
    (fun q => hasFDerivAt_const (c := θ) (x := q)) hjoint
    (fun q => hinit q θ)
    (fun q t ht => (hflow q θ t (uIoo_subset_uIcc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) p
  have hJ (t : ℝ) (ht : t ∈ uIcc a b) :
      deriv (fun η => Θ p t η) θ =
        Real.exp (∫ r in a..t, Dθ (p, (r, Θ p r θ))) := by
    have hjoint' : ContinuousOn (fun z : ℝ × ℝ => Θ p z.2 z.1)
        (univ ×ˢ uIcc a t) :=
      hΘ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn
        (fun z hz => ⟨mem_univ _, uIcc_subset_uIcc_left ht hz.2⟩)
    exact (scalarFlow_hasDerivAt_initialAngle
      (F := fun z : ℝ × ℝ => F (p, z)) (D := fun z : ℝ × ℝ => Dθ (p, z))
      (Θ := fun z : ℝ × ℝ => Θ p z.2 z.1) (a := a) (b := t)
      (hDθ.comp (continuous_const.prodMk continuous_id))
      (fun r x => hangle p r x) hjoint' (hinit p)
      (fun η r hr => (hflow p η r (uIcc_subset_uIcc_left ht hr)).mono
        (uIcc_subset_uIcc_left ht)) θ).deriv
  have htime : ContinuousOn (fun t => Θ p t θ) (uIcc a b) :=
    hjoint.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨mem_univ _, ht⟩)
  have hpath : ContinuousOn (fun t => (p, (t, Θ p t θ))) (uIcc a b) :=
    continuousOn_const.prodMk (continuousOn_id.prodMk htime)
  have hκ : ContinuousOn (fun t => Dθ (p, (t, Θ p t θ))) (uIcc a b) :=
    hDθ.comp_continuousOn hpath
  have hprimitive : ContinuousOn
      (fun t => ∫ r in a..t, Dθ (p, (r, Θ p r θ))) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hκ.intervalIntegrable left_mem_uIcc
  have hw : ContinuousOn (fun t =>
      Real.exp (-(∫ r in a..t, Dθ (p, (r, Θ p r θ)))) •
        Dp (p, (t, Θ p t θ))) (uIcc a b) :=
    (Real.continuous_exp.comp_continuousOn hprimitive.neg).smul
      (hDp.comp_continuousOn hpath)
  rw [hd.fderiv, zero_add, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.intervalIntegral_apply (μ := volume) hw.intervalIntegrable e,
    ← hJ b right_mem_uIcc]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change (Real.exp (-∫ r in a..t, Dθ (p, (r, Θ p r θ))) •
      Dp (p, (t, Θ p t θ))) e =
    Dp (p, (t, Θ p t θ)) e / deriv (fun η => Θ p t η) θ
  rw [hJ t ht, Real.exp_neg, ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
  exact mul_comm _ _

end ContinuousFlexibility.Analysis
