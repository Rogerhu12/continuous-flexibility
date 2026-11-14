module

public import ContinuousFlexibility.Radial.InnerRadialH1Density
public import ContinuousFlexibility.Radial.InnerRadialAffineLift

/-!
# Actual smooth unit-trace fields belong to the physical piece domain

Smoothness is only required in neighborhoods of the closed interval,
as is appropriate for retained Liouville representatives. Subtracting
the fixed affine hat leaves a genuine zero-endpoint field; actual
cutoff density supplies its membership in the common physical closure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable (D : ReferenceData) (hw : Continuous D.w)
  {a b : ℝ} (hab : a < b) (ha : 0 < a)
  (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

include hab in
theorem innerRadialH1Pair_sub_affineUnit {u : ℝ → ℝ}
    (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r) (i : Fin 2)
    (hua : u a = innerEndpointValues i 0) (hub : u b = innerEndpointValues i 1)
    {Q : InnerRadialH1Pair D}
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u)) :
    Q - innerRadialAffineUnitPair D hw ha hcore hpos i ∈ innerRadialH1Zero D a b := by
  let h : ℝ → ℝ := innerIntervalAffineLift a b (innerEndpointValues i)
  have hh : ContDiff ℝ ∞ h := innerIntervalAffineLift_contDiff a b (innerEndpointValues i)
  let φ : ℝ → ℝ := fun r => u r - h r
  have hφ : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ φ r :=
    fun r hr => (hu r hr).sub hh.contDiffAt
  have hends := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  have hφa : φ a = 0 := by
    dsimp only [φ, h]
    rw [hua, hends.1, sub_self]
  have hφb : φ b = 0 := by
    dsimp only [φ, h]
    rw [hub, hends.2, sub_self]
  apply innerRadialH1Zero_of_smooth_zero_endpoints D hw hab ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) hφ hφa hφb
  · filter_upwards [Lp.coeFn_sub Q.1 (innerRadialAffineUnitPair D hw ha hcore hpos i).1,
      hQu, innerRadialAffineUnitPair_value_ae D hw ha hcore hpos i] with r hsub hQ hA
    rw [hsub, Pi.sub_apply, hQ, hA]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, φ, h]
    · simp only [indicator_of_notMem hr, sub_self]
  · filter_upwards [Lp.coeFn_sub Q.2 (innerRadialAffineUnitPair D hw ha hcore hpos i).2,
      hQd, innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos i] with r hsub hQ hA
    rw [hsub, Pi.sub_apply, hQ, hA]
    by_cases hr : r ∈ Ioo a b
    · have hd : deriv φ r = deriv u r - deriv h r :=
        (((hu r (Ioo_subset_Icc_self hr)).differentiableAt (by simp)).hasDerivAt.fun_sub
          (hh.differentiable (by simp) r).hasDerivAt).deriv
      simp only [indicator_of_mem hr, innerGapGradientField, hd]
      dsimp only [h]
      ring
    · simp only [indicator_of_notMem hr, sub_self]

include hab in
theorem innerRadialH1Pair_unit_domain_trace {u : ℝ → ℝ}
    (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r) (i : Fin 2)
    (hua : u a = innerEndpointValues i 0) (hub : u b = innerEndpointValues i 1)
    {Q : InnerRadialH1Pair D}
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u)) :
    Q ∈ innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos Q = innerEndpointValues i := by
  apply (innerRadialH1Domain_trace_iff D hw hab ha hcore hpos Q (innerEndpointValues i)).mpr
  have hA : innerRadialAffineLift D hw ha hcore hpos (innerEndpointValues i) =
      innerRadialAffineUnitPair D hw ha hcore hpos i := by
    fin_cases i <;> norm_num [innerRadialAffineLift_apply, innerEndpointValues]
  rw [hA]
  exact innerRadialH1Pair_sub_affineUnit D hw hab ha hcore hpos hu i hua hub hQu hQd

end ContinuousFlexibility.Radial
