module

public import ContinuousFlexibility.Radial.R11bZeroMode
public import ContinuousFlexibility.Radial.R11bInverseDensity
public import ContinuousFlexibility.Radial.R11bAngularL2Bridge
public import ContinuousFlexibility.Radial.R11bGlobalL2
public import ContinuousFlexibility.Analysis.EndpointWeakUniqueness
public import ContinuousFlexibility.Analysis.IntervalWeakPotential

/-!
# Zero angular channel uniqueness on the maximum physical graph

The left constant is retained in an output realization. On a right endpoint
tail the chosen left cutoff is zero, so the actual angular mean itself has
finite inverse-coefficient L² norm. Endpoint resistance then excludes both
homogeneous zero-mode constants.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_outputMean_inverse_sqrt_memLp_tail {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M aL : ℝ} (hγ : 0 < γ)
    {U : RadialUnknown} (hU : OutputRealization D γ M aL U)
    {x₀ : ℝ} (hx₀ : x₀ ∈ radialCore D)
    (hzero : ∀ r ∈ Ioo x₀ D.b, D.chiLeft r = 0) :
    MemLp (fun r => Real.sqrt ((D.w r)⁻¹) *
      radialAngularMean (fun θ => U.1 (r, θ))) 2 (volume.restrict (Ioo x₀ D.b)) := by
  have hweighted := (r11b_radialAngularMean_L2_bound
    (r11b_outputRemainder_inverse_sqrt_memLp hD hγ hU)).1
  have hsub : Ioo x₀ D.b ⊆ radialCore D :=
    Ioo_subset_Ioo hx₀.1.le le_rfl
  have ht := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hweighted
  apply MemLp.ae_eq _ ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  change radialAngularMean (fun θ =>
    Real.sqrt ((D.w r)⁻¹) * (U.1 (r, θ) - aL * D.chiLeft r)) =
      Real.sqrt ((D.w r)⁻¹) * radialAngularMean (fun θ => U.1 (r, θ))
  rw [hzero r hr]
  simp only [mul_zero, sub_zero]
  exact r11b_radialAngularMean_const_mul _ _

theorem r11b_graph_mean_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ γ' M₀ M₀' M₁ M₁' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ')
    {U V : RadialUnknown} {F : RadialSource}
    (hUF : ReferenceGraph D γ M₀ M₁ U F)
    (hVF : ReferenceGraph D γ' M₀' M₁' V F) :
    (fun r => radialAngularMean (fun θ => U.1 (r, θ)))
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => radialAngularMean (fun θ => V.1 (r, θ))) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  let u : ℝ → ℝ := fun r => radialAngularMean (fun θ => U.1 (r, θ)) -
    radialAngularMean (fun θ => V.1 (r, θ))
  have hu := (r11b_radialAngularMean_L2_bound
    (r11b_output_memLp hD hborder hγ hUF.1)).1
  have hv := (r11b_radialAngularMean_L2_bound
    (r11b_output_memLp hD hborder hγ' hVF.1)).1
  have hdiff : MemLp u 2 (volume.restrict (radialCore D)) := by
    apply MemLp.ae_eq _ (hu.sub hv)
    exact Eventually.of_forall fun _ => rfl
  obtain ⟨ε, hε, _, hχ⟩ := hborder.2.2.2.2.2
  obtain ⟨x₀, hx₀l, hx₀r⟩ := exists_between
    (max_lt hgeom.2.1 (by linarith : D.b - ε < D.b))
  have hx₀ : x₀ ∈ radialCore D := ⟨(le_max_left _ _).trans_lt hx₀l, hx₀r⟩
  have hχtail : ∀ r ∈ Ioo x₀ D.b, D.chiLeft r = 0 := by
    intro r hr
    exact hχ r ⟨(le_max_right _ _).trans_lt (hx₀l.trans hr.1), hr.2⟩
  obtain ⟨aU, haU⟩ := hUF.1
  obtain ⟨aV, haV⟩ := hVF.1
  have htu := r11b_outputMean_inverse_sqrt_memLp_tail hD hγ haU hx₀ hχtail
  have htv := r11b_outputMean_inverse_sqrt_memLp_tail hD hγ' haV hx₀ hχtail
  have htail : MemLp (fun r => Real.sqrt ((D.w r)⁻¹) * u r)
      2 (volume.restrict (Ioo x₀ D.b)) := by
    apply MemLp.ae_eq _ (htu.sub htv)
    exact Eventually.of_forall fun r => by
      change _ - _ = Real.sqrt ((D.w r)⁻¹) *
        (radialAngularMean (fun θ => U.1 (r, θ)) -
          radialAngularMean (fun θ => V.1 (r, θ)))
      ring
  have hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ radialCore D →
        (∫ r, u r * deriv (fun t => D.w t * deriv φ t) r) = 0 := by
    intro φ hφ hφc hφs
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hflux := (contDiff_infty_iff_deriv.mp (hgeom.2.2.1.1.mul hφd)).2.continuous
    have hUi := intervalIntegrable_mul_continuous hgeom.2.1.le hu hflux
    have hVi := intervalIntegrable_mul_continuous hgeom.2.1.le hv hflux
    have hsupport : Function.support
        (fun r => u r * deriv (fun t => D.w t * deriv φ t) r) ⊆ Ioc D.a D.b := by
      apply (Function.support_mul_subset_right u
        (deriv (fun t => D.w t * deriv φ t))).trans
      have hts : tsupport (deriv (fun t => D.w t * deriv φ t)) ⊆ radialCore D :=
        tsupport_deriv_subset.trans
          (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hφs))
      exact (subset_tsupport _).trans (hts.trans Ioo_subset_Ioc_self)
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
    change (∫ r in D.a..D.b,
      (radialAngularMean (fun θ => U.1 (r, θ)) -
        radialAngularMean (fun θ => V.1 (r, θ))) *
          deriv (fun t => D.w t * deriv φ t) r) = 0
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hUi hVi,
      r11b_referenceGraph_mean_equation hUF hφ hφc hφs,
      r11b_referenceGraph_mean_equation hVF hφ hφc hφs, sub_self]
  have hz := weak_divergence_eq_zero_of_tail_memLp hgeom.2.1 hgeom.2.2.1.1
    hgeom.2.2.2.2.1 (hgeom.2.2.1.2 D.b (Or.inr le_rfl))
    (IntegrableOn.locallyIntegrableOn (interval_memLp_integrable hdiff)) hx₀ htail hdiv
  filter_upwards [hz] with r hr
  change radialAngularMean (fun θ => U.1 (r, θ)) -
    radialAngularMean (fun θ => V.1 (r, θ)) = 0 at hr
  exact sub_eq_zero.mp hr

end ContinuousFlexibility.Radial
