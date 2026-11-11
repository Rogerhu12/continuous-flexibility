import ContinuousFlexibility.Analysis.AngularRegularityIntegral

/-!
# Smooth angular dependence from the actual variational equation

Each use of the variational equation gains one angular derivative:
the derivative of the flow is the exponential of a radial primitive.
All operations in that formula preserve continuous angular derivatives.
No radial differentiability is used in this induction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem scalar_flow_angularRegular_closedStrip
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : ∀ n, AngularRegular n
      (fun r θ => closedStripExtend hab.le (fun p => d p.1 p.2) (r, θ)))
    (hvd : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d t θ) θ)
    (hF : ContinuousOn (fun p : PolarPoint => F p.1 p.2) (Icc a b ×ˢ univ))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t) :
    ∀ n, AngularRegular n
      (fun r θ => closedStripExtend hab.le (fun p => F p.1 p.2) (r, θ)) := by
  let ρ : ℝ → ℝ := fun r => projIcc a b hab.le r
  let G : ℝ → ℝ → ℝ := fun r θ => closedStripExtend hab.le (fun p => F p.1 p.2) (r, θ)
  let D : ℝ → ℝ → ℝ := fun r θ => closedStripExtend hab.le (fun p => d p.1 p.2) (r, θ)
  have hρ : Continuous ρ := continuous_subtype_val.comp continuous_projIcc
  have hρmem (r : ℝ) : ρ r ∈ Icc a b := (projIcc a b hab.le r).property
  have hGc : Continuous (fun p : PolarPoint => G p.1 p.2) :=
    continuous_closedStripExtend hab.le hF
  have hdc : ContinuousOn (fun p : PolarPoint => d p.1 p.2) (Icc a b ×ˢ univ) := by
    apply (hd 0).continuous.continuousOn.congr
    intro p hp
    exact (closedStripExtend_eq hab.le (fun p : PolarPoint => d p.1 p.2)
      (p := p) hp.1).symm
  have hGder (r θ : ℝ) : HasDerivAt (G r)
      (Real.exp (∫ s in a..ρ r, D s (G s θ))) θ := by
    have h := scalar_flow_hasDerivAt_exp_integral_on hab hdc hvd hF hinit hode (hρmem r) θ
    have hint : (∫ s in a..ρ r, D s (G s θ)) = ∫ s in a..ρ r, d s (F s θ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (hρmem r).1] at hs
      have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans (hρmem r).2⟩
      simp only [D, G, closedStripExtend, projIcc_of_mem hab.le hs']
    exact (h.congr_deriv (congrArg Real.exp hint.symm)).congr_of_eventuallyEq
      (Eventually.of_forall fun θ' => rfl)
  intro n
  change AngularRegular n G
  induction n with
  | zero => exact hGc
  | succ n ih =>
    have hDn : AngularRegular n D := hd n
    have hJ := (((hDn.comp_angle ih).radial_primitive a).comp_time ρ hρ).exp
    exact ⟨hGc, fun r θ => (hGder r θ).differentiableAt,
      hJ.congr (fun r θ => (hGder r θ).deriv)⟩

/-- Smooth angular dependence at every closed-interval time, including the
terminal return time, follows from smooth angular coefficients. -/
theorem scalar_flow_angular_contDiff_of_angularRegular
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : ∀ n, AngularRegular n
      (fun r θ => closedStripExtend hab.le (fun p => d p.1 p.2) (r, θ)))
    (hvd : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d t θ) θ)
    (hF : ContinuousOn (fun p : PolarPoint => F p.1 p.2) (Icc a b ×ˢ univ))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t)
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (F t) := by
  have h := contDiff_of_angularRegular_all
    (scalar_flow_angularRegular_closedStrip hab hd hvd hF hinit hode) t
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact h.contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun x => by
      change F t x = closedStripExtend hab.le (fun p : PolarPoint => F p.1 p.2) (t, x)
      exact (closedStripExtend_eq hab.le (fun p : PolarPoint => F p.1 p.2)
        (p := (t, x)) ht).symm)

/-- Every actual angular derivative is jointly continuous up to the
closed radial endpoints. -/
theorem scalar_flow_angular_iteratedDeriv_continuousOn
    {a b : ℝ} {v d F : ℝ → ℝ → ℝ} (hab : a < b)
    (hd : ∀ n, AngularRegular n
      (fun r θ => closedStripExtend hab.le (fun p => d p.1 p.2) (r, θ)))
    (hvd : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d t θ) θ)
    (hF : ContinuousOn (fun p : PolarPoint => F p.1 p.2) (Icc a b ×ˢ univ))
    (hinit : ∀ θ, F a θ = θ)
    (hode : ∀ θ t, t ∈ Ioo a b → HasDerivAt (fun s => F s θ) (v t (F t θ)) t)
    (n : ℕ) :
    ContinuousOn (fun p : PolarPoint => iteratedDeriv n (F p.1) p.2)
      (Icc a b ×ˢ univ) := by
  have hreg := scalar_flow_angularRegular_closedStrip hab hd hvd hF hinit hode n
  apply hreg.iteratedDeriv_continuous.continuousOn.congr
  intro p hp
  have heq : (fun θ => closedStripExtend hab.le (fun q : PolarPoint => F q.1 q.2) (p.1, θ)) =
      F p.1 := by
    funext θ
    exact closedStripExtend_eq hab.le (fun q : PolarPoint => F q.1 q.2)
      (p := (p.1, θ)) hp.1
  exact congrArg (fun f : ℝ → ℝ => iteratedDeriv n f p.2) heq.symm

end ContinuousFlexibility.Analysis
