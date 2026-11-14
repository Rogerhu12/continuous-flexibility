module

public import ContinuousFlexibility.Analysis.OperatorJetProbes
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Actual regularity of the mixed coefficient from operator equality

The mixed stored coefficient is not assumed differentiable. If it were
not differentiable, a one-parameter family of globally smooth tests would
have a vanishing radial flux derivative. Every nonzero angular flux
derivative in that family must agree, because the fluxes agree on the
whole angular line. The smooth comparison operator takes two different
nonzero values on the same tests, which excludes this alternative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Actual differentiable functions with the same angular slice have
the same angular partial at the point. -/
theorem angularPartial_eq_of_equal_slice
    {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (hslice : ∀ θ : ℝ, f (p.1, θ) = g (p.1, θ)) :
    angularPartial f p = angularPartial g p := by
  have hline : HasDerivAt (fun θ : ℝ => (p.1, θ)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
  have hfd := hf.hasFDerivAt.comp_hasDerivAt p.2 hline
  have hgd := hg.hasFDerivAt.comp_hasDerivAt p.2 hline
  have he : f ∘ (fun θ : ℝ => (p.1, θ)) = g ∘ (fun θ : ℝ => (p.1, θ)) :=
    funext hslice
  rw [he] at hfd
  exact hfd.unique hgd

private theorem differentiableAt_of_angularPartial_ne_zero
    {f : PolarPoint → ℝ} {p : PolarPoint} (h : angularPartial f p ≠ 0) :
    DifferentiableAt ℝ f p := by
  by_contra hf
  apply h
  simp only [angularPartial, fderiv_zero_of_not_differentiableAt hf,
    ContinuousLinearMap.zero_apply]

/-- Equality of the actual operator action forces differentiability of
the stored mixed coefficient. Only the radial stored coefficient is
assumed differentiable; the angular stored coefficient is arbitrary. -/
theorem differentiableAt_mixedCoefficient_of_operator_action
    {L B : SymmetricCoefficients} {p : PolarPoint}
    (hLa : DifferentiableAt ℝ L.a p)
    (hBa : DifferentiableAt ℝ B.a p) (hBb : DifferentiableAt ℝ B.b p)
    (hBc : DifferentiableAt ℝ B.c p) (hBa0 : B.a p ≠ 0)
    (hop : ∀ u : PolarPoint → ℝ, ContDiff ℝ ∞ u →
      divergenceOperator L u p = divergenceOperator B u p) :
    DifferentiableAt ℝ L.b p := by
  by_contra hLb
  let flux (t : ℝ) (q : PolarPoint) : ℝ :=
    L.b q * (t * (q.1 - p.1)) + L.c q
  have hradial (t : ℝ) : ¬ DifferentiableAt ℝ
      (fun q : PolarPoint => L.a q * (t * (q.1 - p.1)) + L.b q) p := by
    intro hd
    have hs := hd.sub
      (hLa.mul ((differentiableAt_fst.sub (differentiableAt_const p.1)).const_mul t))
    have he : ((fun q : PolarPoint => L.a q * (t * (q.1 - p.1)) + L.b q) -
        L.a * (fun y : PolarPoint =>
          t * ((Prod.fst : PolarPoint → ℝ) - (fun _ : PolarPoint => p.1)) y)) = L.b := by
      funext q
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    rw [he] at hs
    exact hLb hs
  have haction (t : ℝ) :
      divergenceOperator L (operatorJetProbe p t 0 0) p = angularPartial (flux t) p := by
    have hr : radialPartial (operatorJetProbe p t 0 0) = operatorJetProbeRadial p t 0 :=
      funext fun q => (operatorJetProbe_partials p q t 0 0).1
    have ht : angularPartial (operatorJetProbe p t 0 0) = operatorJetProbeAngular p 0 0 :=
      funext fun q => (operatorJetProbe_partials p q t 0 0).2
    have hz : radialPartial
        (fun q : PolarPoint => L.a q * (t * (q.1 - p.1)) + L.b q) p = 0 := by
      simp only [radialPartial, fderiv_zero_of_not_differentiableAt (hradial t),
        ContinuousLinearMap.zero_apply]
    rw [divergenceOperator, hr, ht]
    simpa only [operatorJetProbeRadial, operatorJetProbeAngular, flux,
      zero_mul, add_zero, mul_one, hz, zero_add]
  let d : ℝ := radialPartial B.b p + angularPartial B.c p
  have hvalue (s : ℝ) : angularPartial (flux ((s - d) / B.a p)) p = s := by
    rw [← haction, hop _ (contDiff_operatorJetProbe p ((s - d) / B.a p) 0 0),
      divergenceOperator_operatorJetProbe hBa hBb hBc]
    simp only [mul_zero, add_zero]
    dsimp only [d]
    field_simp [hBa0]
    <;> ring
  have hfirst : DifferentiableAt ℝ (flux ((1 - d) / B.a p)) p :=
    differentiableAt_of_angularPartial_ne_zero (by rw [hvalue]; norm_num)
  have hsecond : DifferentiableAt ℝ (flux ((2 - d) / B.a p)) p :=
    differentiableAt_of_angularPartial_ne_zero (by rw [hvalue]; norm_num)
  have he := angularPartial_eq_of_equal_slice hfirst hsecond
    (fun θ => by simp only [flux, sub_self, mul_zero, zero_add])
  rw [hvalue, hvalue] at he
  norm_num at he

end ContinuousFlexibility.Analysis
