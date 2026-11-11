import ContinuousFlexibility.Analysis.IntervalFluxEnergy
import ContinuousFlexibility.Radial.R11bRadialTests
import ContinuousFlexibility.Radial.R11bTensorL2
import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# The actual weak normal derivative of radial tensors

Compact radial tests restrict to smooth compact tests on every angular slice.
One-dimensional integration by parts and physical Fubini then identify the
normal derivative of a radial C¹ representative times an angular L² function.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_radialTest_slice {D : ReferenceData} {ψ : PolarPoint → ℝ}
    (hψ : RadialTest D ψ) (θ : ℝ) :
    ContDiff ℝ ∞ (fun r => ψ (r, θ)) ∧
      HasCompactSupport (fun r => ψ (r, θ)) ∧
      tsupport (fun r => ψ (r, θ)) ⊆ radialCore D := by
  have hdiff : ContDiff ℝ ∞ (fun r => ψ (r, θ)) :=
    hψ.1.comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨K, hK, hKcore, hzero⟩ := hψ.2.2
  have hs : Function.support (fun r => ψ (r, θ)) ⊆ K := by
    intro r hr
    by_contra hrK
    exact hr (hzero r hrK θ)
  have hts : tsupport (fun r => ψ (r, θ)) ⊆ K :=
    closure_minimal hs hK.isClosed
  exact ⟨hdiff, hK.of_isClosed_subset isClosed_closure hts, hts.trans hKcore⟩

theorem r11b_radialTest_slice_deriv {D : ReferenceData} {ψ : PolarPoint → ℝ}
    (hψ : RadialTest D ψ) (r θ : ℝ) :
    deriv (fun t => ψ (t, θ)) r = radialPartial ψ (r, θ) :=
  (hasDerivAt_radialSlice (hψ.1.differentiable (by simp) (r, θ))).deriv

theorem r11b_scalar_normal_pairing {D : ReferenceData} (hab : D.a < D.b)
    {c d : ℝ → ℝ}
    (hder : ∀ r ∈ radialCore D, HasDerivAt c (d r) r)
    (hd : ContinuousOn d (radialCore D)) {ψ : PolarPoint → ℝ}
    (hψ : RadialTest D ψ) (θ : ℝ) :
    (∫ r in radialCore D, c r * radialPartial ψ (r, θ)) =
      -(∫ r in radialCore D, d r * ψ (r, θ)) := by
  obtain ⟨hφ, hφc, hφs⟩ := r11b_radialTest_slice hψ θ
  have hip := integral_mul_deriv_eq_neg_of_hasDerivAt_Ioo hab hder hd hφ hφc hφs
  have hleft : (∫ r in radialCore D, c r * radialPartial ψ (r, θ)) =
      ∫ r, c r * deriv (fun t => ψ (t, θ)) r := by
    simp_rw [r11b_radialTest_slice_deriv hψ]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hz : radialPartial ψ (r, θ) = 0 := by
      rw [← r11b_radialTest_slice_deriv hψ]
      exact deriv_of_notMem_tsupport (fun hs => hr (hφs hs))
    rw [hz, mul_zero]
  have hright : (∫ r in radialCore D, d r * ψ (r, θ)) =
      ∫ r, d r * ψ (r, θ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hz : ψ (r, θ) = 0 := by
      by_contra hne
      exact hr (hφs (subset_tsupport (fun t => ψ (t, θ)) hne))
    rw [hz, mul_zero]
  rw [hleft, hright]
  exact hip

theorem r11b_weakNormalDerivative_tensor {D : ReferenceData} (hab : D.a < D.b)
    {c d e : ℝ → ℝ}
    (hcLp : MemLp c 2 (volume.restrict (radialCore D)))
    (hdLp : MemLp d 2 (volume.restrict (radialCore D)))
    (heLp : MemLp e 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hder : ∀ r ∈ radialCore D, HasDerivAt c (d r) r)
    (hd : ContinuousOn d (radialCore D)) :
    WeakNormalDerivative D (fun x => c x.1 * e x.2) (fun x => d x.1 * e x.2) := by
  have hU : MemLp (fun x : PolarPoint => c x.1 * e x.2) 2
      (radialPhysicalMeasure D) := by
    rw [r11b_radialPhysicalMeasure_eq_prod]
    exact r11b_memLp_tensor hcLp heLp
  have hV : MemLp (fun x : PolarPoint => d x.1 * e x.2) 2
      (radialPhysicalMeasure D) := by
    rw [r11b_radialPhysicalMeasure_eq_prod]
    exact r11b_memLp_tensor hdLp heLp
  intro ψ hψ
  have hψLp : MemLp ψ 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp hψ.1.continuous
  have hψrLp : MemLp (radialPartial ψ) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (r11b_radialTest_radialPartial hψ).1.continuous
  have hleft := hU.integrable_mul hψrLp
  have hright := hV.integrable_mul hψLp
  rw [r11b_integral_angularMean_mul_eq hab.le hU hψrLp,
    r11b_integral_angularMean_mul_eq hab.le hV hψLp]
  have heq : (∫ x, (c x.1 * e x.2) * radialPartial ψ x ∂radialPhysicalMeasure D) =
      -(∫ x, (d x.1 * e x.2) * ψ x ∂radialPhysicalMeasure D) := by
    rw [r11b_radialPhysicalMeasure_eq_prod] at hleft hright ⊢
    rw [integral_prod_symm _ hleft, integral_prod_symm _ hright, ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by
      have hu : (fun r => (c r * e θ) * radialPartial ψ (r, θ)) =
          (fun r => (c r * radialPartial ψ (r, θ)) * e θ) := by
        funext r
        ring
      have hv : (fun r => (d r * e θ) * ψ (r, θ)) =
          (fun r => (d r * ψ (r, θ)) * e θ) := by
        funext r
        ring
      rw [hu, hv, integral_mul_const, integral_mul_const,
        r11b_scalar_normal_pairing hab hder hd hψ θ]
      ring
  rw [heq]
  ring

theorem r11b_weakNormalDerivative_tensor_of_contDiffOn_one
    {D : ReferenceData} (hab : D.a < D.b) {c e : ℝ → ℝ}
    (hc : ContDiffOn ℝ 1 c (radialCore D))
    (hcLp : MemLp c 2 (volume.restrict (radialCore D)))
    (hdLp : MemLp (deriv c) 2 (volume.restrict (radialCore D)))
    (heLp : MemLp e 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    WeakNormalDerivative D (fun x => c x.1 * e x.2)
      (fun x => deriv c x.1 * e x.2) := by
  apply r11b_weakNormalDerivative_tensor hab hcLp hdLp heLp
  · intro r hr
    exact ((hc.differentiableOn (by simp) r hr).differentiableAt
      (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  · exact continuousOn_deriv_of_contDiffOn_one_Ioo hc

end ContinuousFlexibility.Radial
