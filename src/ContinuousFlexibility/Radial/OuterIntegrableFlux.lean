import ContinuousFlexibility.Radial.OuterIntegrableVariation

/-!
# The flux equation for arbitrary locally integrable sources

The Green value is C¹, while its flux is locally absolutely continuous.
The original radial equation therefore holds as a weak equation for every
locally integrable forcing, including weighted L² forcing.  This file uses
the actual flux of the same variation-of-parameters value function.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Analysis

/-- The explicit flux of the outer variation-of-parameters solution. -/
def outerSolutionFlux (lam cA cB c : ℝ) (w U V f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(1 / lam) * ((w x * deriv V x) * (cA + ∫ t in c..x, U t * f t) +
    (w x * deriv U x) * (cB - ∫ t in c..x, V t * f t))

/-- This is the actual flux of the C¹ value representative. -/
theorem outerSolutionFlux_eq {a b lam cA cB c : ℝ} {w U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    ∀ x ∈ Ioo a b, outerSolutionFlux lam cA cB c w U V f x =
      w x * deriv (outerSolution lam cA cB c U V f) x := by
  intro x hx
  rw [(hasDerivAt_outerSolution_locallyIntegrable hU hV hf hc x hx).deriv]
  unfold outerSolutionFlux
  ring

/-- The flux is absolutely continuous on every compact interior interval. -/
theorem outerSolutionFlux_absolutelyContinuous {a b lam cA cB c : ℝ} {w U V f : ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hU : ContDiffOn ℝ 2 U (Ioo a b)) (hV : ContDiffOn ℝ 2 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b)
    {l r : ℝ} (hl : l ∈ Ioo a b) (hr : r ∈ Ioo a b) :
    AbsolutelyContinuousOnInterval (outerSolutionFlux lam cA cB c w U V f) l r := by
  have hsub := ordConnected_Ioo.uIcc_subset hl hr
  have hDU : ContDiffOn ℝ 1 (deriv U) (Ioo a b) :=
    hU.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDV : ContDiffOn ℝ 1 (deriv V) (Ioo a b) :=
    hV.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hZAC := ((hw.mul hDU).mono hsub).absolutelyContinuousOnInterval
  have hQAC := ((hw.mul hDV).mono hsub).absolutelyContinuousOnInterval
  have hUf : LocallyIntegrableOn (fun x => U x * f x) (Ioo a b) :=
    hf.continuousOn_mul hU.continuousOn isOpen_Ioo.isLocallyClosed
  have hVf : LocallyIntegrableOn (fun x => V x * f x) (Ioo a b) :=
    hf.continuousOn_mul hV.continuousOn isOpen_Ioo.isLocallyClosed
  have hAconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => cA) l r :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => cA)).contDiffOn.absolutelyContinuousOnInterval
  have hBconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => cB) l r :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => cB)).contDiffOn.absolutelyContinuousOnInterval
  have hA := hAconst.fun_add (intervalWeakPrimitive_absolutelyContinuous hUf hc hl hr)
  have hB := hBconst.fun_sub (intervalWeakPrimitive_absolutelyContinuous hVf hc hl hr)
  exact ((hQAC.fun_mul hA).fun_add (hZAC.fun_mul hB)).const_mul (-(1 / lam))

/-- The actual flux solves the inhomogeneous first-order equation almost everywhere. -/
theorem outerSolutionFlux_ae_hasDerivAt {a b J lam cA cB c : ℝ} {w U V f : ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hU : ContDiffOn ℝ 2 U (Ioo a b)) (hV : ContDiffOn ℝ 2 V (Ioo a b))
    (hUeq : ∀ x ∈ Ioo a b, radialJacobi J w U x = 0)
    (hVeq : ∀ x ∈ Ioo a b, radialJacobi J w V x = 0)
    (hW : ∀ x ∈ Ioo a b, radialWronskian w U V x = -lam)
    (hlam : lam ≠ 0) (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b)
    {l r : ℝ} (hl : l ∈ Ioo a b) (hr : r ∈ Ioo a b) :
    ∀ᵐ x ∂volume, x ∈ uIcc l r →
      HasDerivAt (outerSolutionFlux lam cA cB c w U V f)
        (J * deriv w x / x * outerSolution lam cA cB c U V f x + f x) x := by
  have hUf : LocallyIntegrableOn (fun x => U x * f x) (Ioo a b) :=
    hf.continuousOn_mul hU.continuousOn isOpen_Ioo.isLocallyClosed
  have hVf : LocallyIntegrableOn (fun x => V x * f x) (Ioo a b) :=
    hf.continuousOn_mul hV.continuousOn isOpen_Ioo.isLocallyClosed
  have hDU : ContDiffOn ℝ 1 (deriv U) (Ioo a b) :=
    hU.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDV : ContDiffOn ℝ 1 (deriv V) (Ioo a b) :=
    hV.deriv_of_isOpen isOpen_Ioo (by norm_num)
  filter_upwards [intervalWeakPrimitive_ae_hasDerivAt_on hUf hc hl hr,
    intervalWeakPrimitive_ae_hasDerivAt_on hVf hc hl hr] with x hAx hBx hxin
  have hx : x ∈ Ioo a b := ordConnected_Ioo.uIcc_subset hl hr hxin
  have hwd : DifferentiableAt ℝ w x :=
    (hw.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)
  have hZ := hasDerivAt_flux_of_radialJacobi_eq_zero hwd
    ((hDU.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)) (hUeq x hx)
  have hQ := hasDerivAt_flux_of_radialJacobi_eq_zero hwd
    ((hDV.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)) (hVeq x hx)
  have hA := (hasDerivAt_const x cA).add (hAx hxin)
  have hB := (hasDerivAt_const x cB).sub (hBx hxin)
  have hcalc := ((hQ.mul hA).add (hZ.mul hB)).const_mul (-(1 / lam))
  have hWr := hW x hx
  unfold radialWronskian at hWr
  have key : -(1 / lam) * (w x * (U x * deriv V x - deriv U x * V x) * f x) = f x := by
    rw [hWr, show -(1 / lam) * (-lam * f x) = (1 / lam * lam) * f x by ring,
      one_div_mul_cancel hlam, one_mul]
  apply hcalc.congr_deriv
  unfold outerSolution
  simp only [Pi.add_apply, Pi.sub_apply, intervalWeakPrimitive]
  linear_combination key

/-- The radial equation in weak form for every locally integrable source. -/
theorem outerSolutionFlux_weakDerivative {a b J lam cA cB c : ℝ} {w U V f : ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hU : ContDiffOn ℝ 2 U (Ioo a b)) (hV : ContDiffOn ℝ 2 V (Ioo a b))
    (hUeq : ∀ x ∈ Ioo a b, radialJacobi J w U x = 0)
    (hVeq : ∀ x ∈ Ioo a b, radialJacobi J w V x = 0)
    (hW : ∀ x ∈ Ioo a b, radialWronskian w U V x = -lam)
    (hlam : lam ≠ 0) (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    HasIntervalWeakDerivative a b (outerSolutionFlux lam cA cB c w U V f)
      (fun x => J * deriv w x / x * outerSolution lam cA cB c U V f x + f x) := by
  exact hasIntervalWeakDerivative_of_locallyAC_ae (hc.1.trans hc.2)
    (fun l hl r hr => outerSolutionFlux_absolutelyContinuous hw hU hV hf hc hl hr)
    (fun l hl r hr => outerSolutionFlux_ae_hasDerivAt hw hU hV hUeq hVeq hW hlam hf hc hl hr)

end ContinuousFlexibility.Radial
