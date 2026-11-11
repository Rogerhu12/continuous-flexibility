import ContinuousFlexibility.Analysis.IntervalACDerivative
import ContinuousFlexibility.Radial.OuterNormalizedState
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Variation of parameters for locally integrable sources

The value formula already used by the outer Green kernel is locally
absolutely continuous for a locally integrable source.  Its two source
terms cancel in the almost-everywhere derivative, leaving a continuous
function.  The resulting derivative identity therefore holds at every
point.  In particular the exact entrance traces remain valid for L²
sources, without assuming a continuous forcing term.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Analysis

private theorem outer_source_products {a b : ℝ} {U V f : ℝ → ℝ}
    (hU : ContinuousOn U (Ioo a b)) (hV : ContinuousOn V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) :
    LocallyIntegrableOn (fun x => U x * f x) (Ioo a b) ∧
      LocallyIntegrableOn (fun x => V x * f x) (Ioo a b) :=
  ⟨hf.continuousOn_mul hU isOpen_Ioo.isLocallyClosed,
    hf.continuousOn_mul hV isOpen_Ioo.isLocallyClosed⟩

/-- Local absolute continuity of the actual variation-of-parameters formula. -/
theorem outerSolution_absolutelyContinuous {a b lam cA cB c : ℝ} {U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b)
    {l r : ℝ} (hl : l ∈ Ioo a b) (hr : r ∈ Ioo a b) :
    AbsolutelyContinuousOnInterval (outerSolution lam cA cB c U V f) l r := by
  have hsub := ordConnected_Ioo.uIcc_subset hl hr
  have hUAC := (hU.mono hsub).absolutelyContinuousOnInterval
  have hVAC := (hV.mono hsub).absolutelyContinuousOnInterval
  obtain ⟨hUf, hVf⟩ := outer_source_products hU.continuousOn hV.continuousOn hf
  have hAconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => cA) l r :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => cA)).contDiffOn.absolutelyContinuousOnInterval
  have hBconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => cB) l r :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => cB)).contDiffOn.absolutelyContinuousOnInterval
  have hA := hAconst.fun_add (intervalWeakPrimitive_absolutelyContinuous hUf hc hl hr)
  have hB := hBconst.fun_sub (intervalWeakPrimitive_absolutelyContinuous hVf hc hl hr)
  exact ((hVAC.fun_mul hA).fun_add (hUAC.fun_mul hB)).const_mul (-(1 / lam))

/-- The continuous expression left after the two source terms cancel. -/
theorem continuousOn_outerSolution_derivative {a b lam cA cB c : ℝ} {U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    ContinuousOn (fun x => -(1 / lam) *
      (deriv V x * (cA + ∫ t in c..x, U t * f t) +
        deriv U x * (cB - ∫ t in c..x, V t * f t))) (Ioo a b) := by
  obtain ⟨hUf, hVf⟩ := outer_source_products hU.continuousOn hV.continuousOn hf
  have hA : ContinuousOn (fun x => cA + ∫ t in c..x, U t * f t) (Ioo a b) :=
    continuousOn_const.add (continuousOn_intervalWeakPrimitive hUf hc)
  have hB : ContinuousOn (fun x => cB - ∫ t in c..x, V t * f t) (Ioo a b) :=
    continuousOn_const.sub (continuousOn_intervalWeakPrimitive hVf hc)
  exact continuousOn_const.mul
    (((hV.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mul hA).add
      ((hU.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mul hB))

/-- The first derivative formula holds pointwise for locally integrable forcing. -/
theorem hasDerivAt_outerSolution_locallyIntegrable {a b lam cA cB c : ℝ} {U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    ∀ x ∈ Ioo a b, HasDerivAt (outerSolution lam cA cB c U V f)
      (-(1 / lam) * (deriv V x * (cA + ∫ t in c..x, U t * f t) +
        deriv U x * (cB - ∫ t in c..x, V t * f t))) x := by
  apply hasDerivAt_of_locallyAC_ae
    (fun l hl r hr => outerSolution_absolutelyContinuous hU hV hf hc hl hr)
    (continuousOn_outerSolution_derivative hU hV hf hc)
  intro l hl r hr
  obtain ⟨hUf, hVf⟩ := outer_source_products hU.continuousOn hV.continuousOn hf
  filter_upwards [intervalWeakPrimitive_ae_hasDerivAt_on hUf hc hl hr,
    intervalWeakPrimitive_ae_hasDerivAt_on hVf hc hl hr] with x hAx hBx hxin
  have hx : x ∈ Ioo a b := ordConnected_Ioo.uIcc_subset hl hr hxin
  have hUd : HasDerivAt U (deriv U x) x :=
    ((hU.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hVd : HasDerivAt V (deriv V x) x :=
    ((hV.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hA := (hasDerivAt_const x cA).add (hAx hxin)
  have hB := (hasDerivAt_const x cB).sub (hBx hxin)
  exact (((hVd.mul hA).add (hUd.mul hB)).const_mul (-(1 / lam))).congr_deriv (by
    simp only [Pi.add_apply, Pi.sub_apply, intervalWeakPrimitive]
    ring)

/-- The canonical value representative is genuinely C¹ in the interior. -/
theorem contDiffOn_outerSolution_locallyIntegrable {a b lam cA cB c : ℝ} {U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    ContDiffOn ℝ 1 (outerSolution lam cA cB c U V f) (Ioo a b) := by
  have hd := hasDerivAt_outerSolution_locallyIntegrable
    (lam := lam) (cA := cA) (cB := cB) hU hV hf hc
  have hdc := continuousOn_outerSolution_derivative
    (lam := lam) (cA := cA) (cB := cB) hU hV hf hc
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply hdc.congr
  intro x hx
  exact (hd x hx).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)

/-- The entrance state identity holds for locally integrable, in particular L², sources. -/
theorem outerSolution_base_state_locallyIntegrable {a b lam cB c : ℝ} {w U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b) :
    outerFluxState lam w (outerSolution lam 0 cB c U V f) c =
      (-(cB / lam)) • outerFluxState lam w U c := by
  have hd := hasDerivAt_outerSolution_locallyIntegrable
    (lam := lam) (cA := 0) (cB := cB) hU hV hf hc c hc
  apply Prod.ext
  · exact outerSolution_base
  · change w c * deriv (outerSolution lam 0 cB c U V f) c / lam =
      (-(cB / lam)) * (w c * deriv U c / lam)
    rw [hd.deriv]
    simp only [intervalIntegral.integral_same]
    ring

/-- Both entrance traces, with no continuity assumption on the forcing and
no division by the natural solution's boundary value. -/
theorem outerSolution_traces_locallyIntegrable {a b lam cB c : ℝ} {w U V f : ℝ → ℝ}
    {v : ℝ × ℝ} (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b)) (hc : c ∈ Ioo a b)
    (hstate : outerFluxState lam w U c = outerStatePerp v) :
    outerStatePair v (outerFluxState lam w (outerSolution lam 0 cB c U V f) c) = 0 ∧
      outerStatePair (outerStatePerp v)
        (outerFluxState lam w (outerSolution lam 0 cB c U V f) c) = -(cB / lam) := by
  rw [outerSolution_base_state_locallyIntegrable hU hV hf hc, hstate]
  constructor
  · change v.1 * (-(cB / lam) * (-v.2)) + v.2 * (-(cB / lam) * v.1) = 0
    ring
  · change (-v.2) * (-(cB / lam) * (-v.2)) + v.1 * (-(cB / lam) * v.1) = -(cB / lam)
    nlinarith [congrArg (fun t : ℝ => -(cB / lam) * t) hv]

end ContinuousFlexibility.Radial
