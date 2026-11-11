import ContinuousFlexibility.Analysis.ScalarFlowParameterFDeriv
import ContinuousFlexibility.Analysis.ScalarFlowTimeChange
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Joint smoothness of an actual scalar flow

The parameter derivative comes from exact trajectory secants. Together
with the given time equation, it yields the actual joint Fréchet
derivative. Finite-order integration then bootstraps this derivative to
every order. A smooth time change applies the result to a supplied closed
time interval, including its terminal slice.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- Genuine parameter and time partial derivatives of order n assemble
to genuine joint regularity of order n+1. -/
theorem contDiff_succ_of_parameter_time_derivatives
    {f : P × ℝ → ℝ} {A : P × ℝ → P →L[ℝ] ℝ} {B : P × ℝ → ℝ} {n : ℕ}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B)
    (hparameter : ∀ p : P, ∀ t : ℝ,
      HasFDerivAt (fun q => f (q, t)) (A (p, t)) p)
    (htime : ∀ p : P, ∀ t : ℝ,
      HasDerivAt (fun r => f (p, r)) (B (p, t)) t) :
    ContDiff ℝ (n + 1) f := by
  let C : P × ℝ → ℝ →L[ℝ] ℝ := fun z =>
    ContinuousLinearMap.toSpanSingleton ℝ (B z)
  have hC : ContDiff ℝ n C := by
    apply contDiff_clm_apply_iff.mpr
    intro r
    simpa only [C, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      (contDiff_const.mul hB : ContDiff ℝ n (fun z => r * B z))
  let D : P × ℝ → (P × ℝ) →L[ℝ] ℝ := fun z => (A z).coprod (C z)
  have hD : ContDiff ℝ n D := by
    apply contDiff_clm_apply_iff.mpr
    intro w
    simpa only [D, C, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      ((hA.clm_apply contDiff_const).add (contDiff_const.mul hB) :
        ContDiff ℝ n (fun z => A z w.1 + w.2 * B z))
  refine contDiff_succ_iff_hasFDerivAt.mpr ⟨D, hD, ?_⟩
  intro z
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun p t => f (p, t))
    (f₁ := fun p t => A (p, t))
    (f₂ := fun p t => ContinuousLinearMap.toSpanSingleton ℝ (B (p, t)))
    (Eventually.of_forall (fun q => hparameter q.1 q.2))
    (Eventually.of_forall (fun q => (htime q.1 q.2).hasFDerivAt))
    hA.continuous.continuousAt hC.continuous.continuousAt).hasFDerivAt

/-- A jointly continuous global family satisfying the actual scalar
ODE and smooth initial data is jointly smooth in all parameters and time. -/
theorem contDiff_scalarFlow
    {F : P × (ℝ × ℝ) → ℝ} {Θ : P × ℝ → ℝ} {v : P → ℝ}
    (hF : ContDiff ℝ ∞ F) (hv : ContDiff ℝ ∞ v) (hΘ : Continuous Θ)
    (hinit : ∀ p : P, Θ (p, 0) = v p)
    (hflow : ∀ p : P, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) t) :
    ContDiff ℝ ∞ Θ := by
  let Dθ : P × (ℝ × ℝ) → ℝ := fun z => (fderiv ℝ F z) (0, (0, 1))
  let Dp : P × (ℝ × ℝ) → P →L[ℝ] ℝ := fun z =>
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P (ℝ × ℝ))
  let Dv : P → P →L[ℝ] ℝ := fderiv ℝ v
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have hDθ : ContDiff ℝ ∞ Dθ := hDF.clm_apply contDiff_const
  have hDp : ContDiff ℝ ∞ Dp := hDF.clm_comp contDiff_const
  have hDv : ContDiff ℝ ∞ Dv := hv.fderiv_right (m := ∞) (by simp)
  have hangle (p : P) (t x : ℝ) :
      HasDerivAt (fun y => F (p, (t, y))) (Dθ (p, (t, x))) x := by
    have hcurve : HasDerivAt (fun y : ℝ => (p, (t, y))) (0, (0, 1)) x := by
      simpa only [id_eq] using
        HasDerivAt.prodMk (hasDerivAt_const (x := x) (c := p))
          (HasDerivAt.prodMk (hasDerivAt_const (x := x) (c := t)) (hasDerivAt_id x))
    have hd := (hF.differentiable (by simp) (p, (t, x))).hasFDerivAt.comp_hasDerivAt x hcurve
    have he : F ∘ (fun y : ℝ => (p, (t, y))) = (fun y => F (p, (t, y))) := by
      funext y
      exact Function.comp_apply
    rw [he] at hd
    exact hd
  have hparameter (p : P) (t x : ℝ) :
      HasFDerivAt (fun q => F (q, (t, x))) (Dp (p, (t, x))) p := by
    have hd := (hF.differentiable (by simp) (p, (t, x))).hasFDerivAt.comp p
      (hasFDerivAt_prodMk_left p (t, x))
    have he : F ∘ (fun q : P => (q, (t, x))) = (fun q => F (q, (t, x))) := by
      funext q
      exact Function.comp_apply
    rw [he] at hd
    exact hd
  have hvalue (p : P) : HasFDerivAt v (Dv p) p :=
    (hv.differentiable (by simp) p).hasFDerivAt
  let K : P × ℝ → ℝ := fun z => Dθ (z.1, (z.2, Θ z))
  let Q : P × ℝ → P →L[ℝ] ℝ := fun z => Dp (z.1, (z.2, Θ z))
  let I : P × ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z.2, K (z.1, t)
  let J : P × ℝ → P →L[ℝ] ℝ := fun z =>
    ∫ t in (0 : ℝ)..z.2, Real.exp (-I (z.1, t)) • Q (z.1, t)
  let B : P × ℝ → P →L[ℝ] ℝ := fun z =>
    Real.exp (I z) • (Dv z.1 + J z)
  have hparam (p : P) (t : ℝ) :
      HasFDerivAt (fun q => Θ (q, t)) (B (p, t)) p :=
    scalarFlow_hasFDerivAt_parameter (a := 0) (b := t)
      hDθ.continuous hDp.continuous hDv.continuous hangle hparameter hvalue
      hΘ.continuousOn hinit (fun q r _ => hflow q r) p
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hΘ
  | succ n ih =>
    have hA : ContDiff ℝ n (fun z : P × ℝ => F (z.1, (z.2, Θ z))) :=
      (contDiff_infty.mp hF n).comp (contDiff_fst.prodMk (contDiff_snd.prodMk ih))
    have hK : ContDiff ℝ n K :=
      (contDiff_infty.mp hDθ n).comp (contDiff_fst.prodMk (contDiff_snd.prodMk ih))
    have hQ : ContDiff ℝ n Q :=
      (contDiff_infty.mp hDp n).comp (contDiff_fst.prodMk (contDiff_snd.prodMk ih))
    have hI : ContDiff ℝ n I := contDiff_parametric_primitive_nat hK (0 : ℝ)
    have hJ : ContDiff ℝ n J :=
      contDiff_parametric_primitive_nat ((Real.contDiff_exp.comp hI.neg).smul hQ) (0 : ℝ)
    have hB : ContDiff ℝ n B :=
      (Real.contDiff_exp.comp hI).smul
        (((contDiff_infty.mp hDv n).comp contDiff_fst).add hJ)
    exact contDiff_succ_of_parameter_time_derivatives hB hA hparam hflow

/-- The actual compact-interval family becomes jointly smooth after
the explicit time change, including both original endpoint slices. -/
theorem contDiff_scalarFlow_timeChange
    {F : P × (ℝ × ℝ) → ℝ} {Θ : P × ℝ → ℝ} {v : P → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ ∞ F) (hv : ContDiff ℝ ∞ v)
    (hΘ : ContinuousOn Θ (univ ×ˢ uIcc a b))
    (hinit : ∀ p : P, Θ (p, a) = v p)
    (hflow : ∀ p t, t ∈ uIcc a b →
      HasDerivWithinAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) (uIcc a b) t) :
    ContDiff ℝ ∞ (scalarFlowTimeChange Θ a b) :=
  contDiff_scalarFlow (contDiff_scalarFieldTimeChange hF a b) hv
    (continuous_scalarFlowTimeChange hΘ)
    (fun p => (scalarFlowTimeChange_initial Θ a b p).trans (hinit p))
    (scalarFlowTimeChange_hasDerivAt hflow)

/-- In particular, the true endpoint flow is smooth in every external
parameter and in any initial angle included among those parameters. -/
theorem contDiff_scalarFlow_endpoint
    {F : P × (ℝ × ℝ) → ℝ} {Θ : P × ℝ → ℝ} {v : P → ℝ} {a b : ℝ}
    (hF : ContDiff ℝ ∞ F) (hv : ContDiff ℝ ∞ v)
    (hΘ : ContinuousOn Θ (univ ×ˢ uIcc a b))
    (hinit : ∀ p : P, Θ (p, a) = v p)
    (hflow : ∀ p t, t ∈ uIcc a b →
      HasDerivWithinAt (fun r => Θ (p, r)) (F (p, (t, Θ (p, t)))) (uIcc a b) t) :
    ContDiff ℝ ∞ (fun p => Θ (p, b)) := by
  have h : ContDiff ℝ ∞ (fun p : P => scalarFlowTimeChange Θ a b (p, 1)) :=
    (contDiff_scalarFlow_timeChange hF hv hΘ hinit hflow).comp
      (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : P => (1 : ℝ))))
  have he : (fun p : P => scalarFlowTimeChange Θ a b (p, 1)) =
      fun p : P => Θ (p, b) :=
    funext (scalarFlowTimeChange_final Θ a b)
  rw [he] at h
  exact h

end ContinuousFlexibility.Analysis
