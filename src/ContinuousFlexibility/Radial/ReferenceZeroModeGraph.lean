import ContinuousFlexibility.Radial.ReferenceLocalL2
import ContinuousFlexibility.Radial.ZeroModeWeakRegularity
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The actual zero channel of the two-dimensional weak graph

Radial test functions belong to the frozen two-dimensional test class.
Their angularly constant channel has no border term. The resulting weak
equation is then restricted to interior intervals and joined to the
locally integrable zero-mode regularity theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem radialAngularMean_mul_const (f : ℝ → ℝ) (c : ℝ) :
    radialAngularMean (fun θ => f θ * c) = radialAngularMean f * c := by
  unfold radialAngularMean
  rw [intervalIntegral.integral_mul_const]
  ring

theorem radialTest_radial_lift {D : ReferenceData} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ radialCore D) :
    RadialTest D (fun x => ψ x.1) := by
  refine ⟨hψ.comp contDiff_fst, ?_, tsupport ψ, hcψ, hψs, ?_⟩
  · intro x
    simp only [Prod.fst_add, add_zero]
  · intro r hr θ
    exact image_eq_zero_of_notMem_tsupport hr

theorem radialWeakPairing_radial_lift (D : ReferenceData)
    (u : PolarPoint → ℝ) (ψ : ℝ → ℝ) :
    radialWeakPairing D u (fun x => ψ x.1) =
      ∫ r in D.a..D.b,
        radialAngularMean (fun θ => u (r, θ)) *
          deriv (fun t => D.w t * deriv ψ t) r := by
  have hd (r : ℝ) : deriv (fun _ : ℝ => ψ r) = (fun _ : ℝ => (0 : ℝ)) := by
    funext θ
    exact deriv_const θ (ψ r)
  unfold radialWeakPairing
  simp only [Radial.radialPDE, hd, deriv_const, mul_zero, add_zero,
    radialAngularMean_mul_const]

theorem referenceColumn_radial_lift_mean (D : ReferenceData)
    (ψ : ℝ → ℝ) (r : ℝ) :
    radialAngularMean (fun θ =>
      referenceColumn D r * Radial.cosineMode 2 θ * ψ r) = 0 := by
  have heq : (fun θ => referenceColumn D r * Radial.cosineMode 2 θ * ψ r) =
      (fun θ => (referenceColumn D r * ψ r) * Radial.cosineMode 2 θ) := by
    funext θ
    ring
  rw [heq, radialAngularMean_const_mul]
  have hz : radialAngularMean (Radial.cosineMode 2) = 0 := by
    simpa only [radialAngularMean, Radial.angularAverage, one_div] using
      Radial.angularAverage_cosineMode 2 (by norm_num)
  rw [hz, mul_zero]

/-- Radial tests in the actual graph give the genuine one-dimensional
divergence equation for the angular mean. -/
theorem ReferenceGraph.zeroModeWeak_global {D : ReferenceData}
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ radialCore D) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => U.1 (r, θ)) *
      deriv (fun t => D.w t * deriv ψ t) r) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => F.1 (r, θ)) * ψ r := by
  have h := hG.2.2.2 (fun x => ψ x.1) (radialTest_radial_lift hψ hcψ hψs)
  simpa only [radialWeakPairing_radial_lift, referenceColumn_radial_lift_mean,
    intervalIntegral.integral_zero, mul_zero, add_zero, radialAngularMean_mul_const] using h

theorem ReferenceGraph.zeroModeWeak_local {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F)
    {l h : ℝ} (hal : D.a < l) (hlh : l < h) (hhb : h < D.b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo l h) :
    (∫ r in l..h, radialAngularMean (fun θ => U.1 (r, θ)) *
      deriv (fun t => D.w t * deriv ψ t) r) =
      ∫ r in l..h, radialAngularMean (fun θ => F.1 (r, θ)) * ψ r := by
  have hsub : Ioo l h ⊆ radialCore D :=
    fun r hr => ⟨hal.trans hr.1, hr.2.trans hhb⟩
  have hleft : Function.support (fun r =>
      radialAngularMean (fun θ => U.1 (r, θ)) *
        deriv (fun t => D.w t * deriv ψ t) r) ⊆ Ioo l h := by
    intro r hr
    have hd : deriv (fun t => D.w t * deriv ψ t) r ≠ 0 :=
      fun hz => hr (by
        change radialAngularMean (fun θ => U.1 (r, θ)) *
          deriv (fun t => D.w t * deriv ψ t) r = 0
        rw [hz, mul_zero])
    exact hψs (tsupport_deriv_subset
      (tsupport_mul_subset_right (support_deriv_subset hd)))
  have hright : Function.support (fun r =>
      radialAngularMean (fun θ => F.1 (r, θ)) * ψ r) ⊆ Ioo l h := by
    intro r hr
    have hne : ψ r ≠ 0 := fun hz => hr (by
      change radialAngularMean (fun θ => F.1 (r, θ)) * ψ r = 0
      rw [hz, mul_zero])
    exact hψs (subset_tsupport ψ hne)
  have heq := hG.zeroModeWeak_global hψ hcψ (hψs.trans hsub)
  rw [Radial.intervalIntegral_eq_integral_of_support_subset hab (hleft.trans hsub),
    Radial.intervalIntegral_eq_integral_of_support_subset hab (hright.trans hsub)] at heq
  rw [Radial.intervalIntegral_eq_integral_of_support_subset hlh.le hleft,
    Radial.intervalIntegral_eq_integral_of_support_subset hlh.le hright]
  exact heq

/-- Every homogeneous output in the actual maximum weak graph has an
angular mean equal almost everywhere to an affine resistance profile.
The remaining endpoint exclusion is a weighted integrability question. -/
theorem ReferenceGraph.zeroMode_ae_affine_resistance {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {U : RadialUnknown}
    (hG : ReferenceGraph D γ M₀ M₁ U 0) :
    ∃ c d : ℝ,
      (fun r => radialAngularMean (fun θ => U.1 (r, θ))) =ᵐ[volume.restrict (radialCore D)]
        (fun r => c + d * Radial.zeroModeResistance ((D.a + D.b) / 2) D.w r) := by
  have hg := Radial.matchingProfileGeometry hD
  apply Radial.zeroModeWeak_ae_affine_resistance hg.2.1
  · intro l h hal hlh hhb
    exact hG.1.angularMean_intervalIntegrable hD hB hlh.le
      (fun r hr => ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩)
  · exact hg.2.2.1.1
  · intro r hr
    exact (hg.2.2.2.2.1 r hr).ne'
  · intro l h hal hlh hhb ψ hψ hcψ hψs
    have heq := hG.zeroModeWeak_local hg.2.1.le hal hlh hhb hψ hcψ hψs
    simpa only [Prod.fst_zero, Pi.zero_apply, radialAngularMean,
      intervalIntegral.integral_zero, mul_zero, zero_mul] using heq

end ContinuousFlexibility.Statements
