module

public import ContinuousFlexibility.Radial.InnerRadialH1Density
public import ContinuousFlexibility.Radial.InnerRadialAffineLift

/-!
# Smooth tests in the actual physical first-order domain

Arbitrary smooth endpoint data are realized by the existing affine lift.
Subtracting it leaves a smooth field with zero endpoint values, so the
proved physical cutoff density puts that residual in the actual closure.
This supplies the tests needed to compare the finite weak graph with the
modal equation; no new test domain is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchedInner_affine_deriv (a b : ℝ) (z : Fin 2 → ℝ) (x : ℝ) :
    deriv (innerIntervalAffineLift a b z) x = (z 1 - z 0) / (b - a) := by
  have he : innerIntervalAffineLift a b z =
      fun r : ℝ => ((z 1 - z 0) / (b - a)) * r +
        (b * z 0 - a * z 1) / (b - a) := by
    funext r
    simp only [innerIntervalAffineLift, div_eq_mul_inv]
    ring
  rw [he]
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id x).const_mul ((z 1 - z 0) / (b - a))).add_const
      ((b * z 0 - a * z 1) / (b - a))).deriv

section Affine

variable (D : ReferenceData) (hw : Continuous D.w) {a b : ℝ}
  (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

theorem matchedInner_affineLift_value_ae (z : Fin 2 → ℝ) :
    ((innerRadialAffineLift D hw ha hcore hpos z).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator (innerIntervalAffineLift a b z) := by
  let A₀ := innerRadialAffineUnitPair D hw ha hcore hpos 0
  let A₁ := innerRadialAffineUnitPair D hw ha hcore hpos 1
  change ((z 0 • A₀.1 + z 1 • A₁.1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add (z 0 • A₀.1) (z 1 • A₁.1),
    Lp.coeFn_smul (z 0) A₀.1, Lp.coeFn_smul (z 1) A₁.1,
    innerRadialAffineUnitPair_value_ae D hw ha hcore hpos 0,
    innerRadialAffineUnitPair_value_ae D hw ha hcore hpos 1]
      with r hadd h₀ h₁ hA₀ hA₁
  rw [hadd, Pi.add_apply, h₀, h₁, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, hA₀, hA₁]
  by_cases hr : r ∈ Ioo a b
  · simp only [indicator_of_mem hr, innerIntervalAffineLift, innerEndpointValues]
    norm_num
    <;> ring
  · simp only [indicator_of_notMem hr, mul_zero, add_zero]

theorem matchedInner_affineLift_gradient_ae (z : Fin 2 → ℝ) :
    ((innerRadialAffineLift D hw ha hcore hpos z).2 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator
        (innerGapGradientField (innerIntervalAffineLift a b z)) := by
  let A₀ := innerRadialAffineUnitPair D hw ha hcore hpos 0
  let A₁ := innerRadialAffineUnitPair D hw ha hcore hpos 1
  change ((z 0 • A₀.2 + z 1 • A₁.2 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add (z 0 • A₀.2) (z 1 • A₁.2),
    Lp.coeFn_smul (z 0) A₀.2, Lp.coeFn_smul (z 1) A₁.2,
    innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos 0,
    innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos 1]
      with r hadd h₀ h₁ hA₀ hA₁
  rw [hadd, Pi.add_apply, h₀, h₁, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, hA₀, hA₁]
  by_cases hr : r ∈ Ioo a b
  · simp only [indicator_of_mem hr, innerGapGradientField, matchedInner_affine_deriv,
      innerEndpointValues]
    norm_num
    <;> ring
  · simp only [indicator_of_notMem hr, mul_zero, add_zero]

/-- The actual smooth field and gradient have their actual endpoint
values in the existing first-order domain, with arbitrary traces. -/
theorem matchedInnerH1Pair_smooth_domain_trace (hab : a < b)
    {u : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    {Q : InnerRadialH1Pair D}
    (hQu : (Q.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u)
    (hQd : (Q.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u)) :
    Q ∈ innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos Q = (fun i => if i = 0 then u a else u b) := by
  let z : Fin 2 → ℝ := fun i => if i = 0 then u a else u b
  let h : ℝ → ℝ := innerIntervalAffineLift a b z
  have hh : ContDiff ℝ ∞ h := innerIntervalAffineLift_contDiff a b z
  let v : ℝ → ℝ := fun r => u r - h r
  have hv : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ v r :=
    fun r hr => (hu r hr).sub hh.contDiffAt
  have hends := innerIntervalAffineLift_endpoints hab z
  have hva : v a = 0 := by
    dsimp only [v, h]
    rw [hends.1]
    simp only [z, if_pos rfl, sub_self]
  have hvb : v b = 0 := by
    dsimp only [v, h]
    rw [hends.2]
    simp only [z, show (1 : Fin 2) ≠ 0 by decide, if_false, sub_self]
  apply (innerRadialH1Domain_trace_iff D hw hab ha hcore hpos Q z).mpr
  apply innerRadialH1Zero_of_smooth_zero_endpoints D hw hab ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) hv hva hvb
  · filter_upwards [Lp.coeFn_sub Q.1 (innerRadialAffineLift D hw ha hcore hpos z).1,
      hQu, matchedInner_affineLift_value_ae D hw ha hcore hpos z]
      with r hsub hQ hA
    rw [hsub, Pi.sub_apply, hQ, hA]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, v, h]
    · simp only [indicator_of_notMem hr, sub_self]
  · filter_upwards [Lp.coeFn_sub Q.2 (innerRadialAffineLift D hw ha hcore hpos z).2,
      hQd, matchedInner_affineLift_gradient_ae D hw ha hcore hpos z]
      with r hsub hQ hA
    rw [hsub, Pi.sub_apply, hQ, hA]
    by_cases hr : r ∈ Ioo a b
    · have hd : deriv v r = deriv u r - deriv h r :=
        (((hu r (Ioo_subset_Icc_self hr)).differentiableAt (by simp)).hasDerivAt.fun_sub
          (hh.differentiable (by simp) r).hasDerivAt).deriv
      simp only [indicator_of_mem hr, innerGapGradientField, hd]
      dsimp only [h]
      ring
    · simp only [indicator_of_notMem hr, sub_self]

end Affine

end ContinuousFlexibility.Radial
