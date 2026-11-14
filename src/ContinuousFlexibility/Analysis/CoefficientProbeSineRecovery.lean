module

public import ContinuousFlexibility.Analysis.CoefficientProbeFieldRegularity
public import ContinuousFlexibility.Analysis.AngularSineMixedBounds
public import ContinuousFlexibility.Analysis.CanonicalCutAxis

/-!
# Genuine sine recovery of the two coefficient probe fields

The fixed two-axis normalization supplies the zero values required by
the genuine smooth sine quotient. Periodicity transports these values
and the actual first angular zero jets to every sine zero. On an open
radial region where the original axis values vanish, the normalization
preserves every germ. The quotient therefore has exactly the one- or
two-order bound of its original numerator on that whole radial region.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem periodicField_zero_at_doubledSineZeros
    {F : PolarPoint → ℝ} (hperiod : Function.Periodic F (0, Real.pi))
    (hzero : ∀ r : ℝ, F (r, 0) = 0 ∧ F (r, Real.pi / 2) = 0)
    {c : ℝ} (hc : Real.sin (2 * c) = 0) (r : ℝ) : F (r, c) = 0 := by
  obtain ⟨side, k, hk⟩ := exists_axisAngle_int_translate_of_sin_two_eq_zero hc
  have hp : Function.Periodic (fun θ : ℝ => F (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hperiod (r, θ)
  have he : F (r, canonicalAxisAngle side + (k : ℝ) * Real.pi) =
      F (r, canonicalAxisAngle side) := hp.int_mul k (canonicalAxisAngle side)
  rw [hk, he]
  cases side
  · exact (hzero r).1
  · exact (hzero r).2

theorem coefficientProbeField_firstJet_zero_at_doubledSineZeros
    {D : ReferenceData} {F : PolarPoint → ℝ}
    (hF : CoefficientProbeFieldRegularity D F)
    {c : ℝ} (hc : Real.sin (2 * c) = 0) (r : ℝ) :
    mixedDerivative 0 1 F (r, c) = 0 := by
  have hjet : mixedDerivative 0 1 F = angularPartial F := by
    funext p
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one] using
      (Radial.hasDerivAt_angularSlice (hF.1.differentiable (by simp) p)).deriv
  have hperiod : Function.Periodic (mixedDerivative 0 1 F) (0, Real.pi) := by
    rw [hjet]
    exact periodic_angularPartial hF.2.2.1
  exact periodicField_zero_at_doubledSineZeros hperiod
    (coefficientProbeField_axis_firstJets hF) hc r

def coefficientProbeSineQuotient (square : Bool) (F : PolarPoint → ℝ) :
    PolarPoint → ℝ :=
  angularSineQuotient square (coefficientAxisNormalize F)

theorem contDiff_coefficientProbeSineQuotient
    {D : ReferenceData} {F : PolarPoint → ℝ}
    (hF : CoefficientProbeFieldRegularity D F) (square : Bool) :
    ContDiff ℝ ∞ (coefficientProbeSineQuotient square F) := by
  have hN := coefficientAxisNormalize_fieldRegularity hF
  exact contDiff_angularSineQuotient hN.1 square
    (fun c hc r => periodicField_zero_at_doubledSineZeros hN.2.2.1
      (coefficientAxisNormalize_axis_values F) hc r)
    (fun _ c hc r => coefficientProbeField_firstJet_zero_at_doubledSineZeros hN hc r)

theorem coefficientProbeSineQuotient_factor
    {D : ReferenceData} {F : PolarPoint → ℝ}
    (hF : CoefficientProbeFieldRegularity D F) (square : Bool) (p : PolarPoint) :
    coefficientAxisNormalize F p =
      Real.sin (2 * p.2) ^ sineFactorOrder square * coefficientProbeSineQuotient square F p := by
  have hN := coefficientAxisNormalize_fieldRegularity hF
  exact angularSineQuotient_factor square
    (fun c hc r => periodicField_zero_at_doubledSineZeros hN.2.2.1
      (coefficientAxisNormalize_axis_values F) hc r) p

theorem coefficientProbeSineQuotient_eq_div_on_radial_region
    {F : PolarPoint → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hzero : ∀ r ∈ J, F (r, 0) = 0 ∧ F (r, Real.pi / 2) = 0)
    (square : Bool) {p : PolarPoint} (hp : p.1 ∈ J)
    (haxis : Real.sin (2 * p.2) ≠ 0) :
    coefficientProbeSineQuotient square F p = F p / Real.sin (2 * p.2) ^ sineFactorOrder square := by
  have he := (coefficientAxisNormalize_eventuallyEq hJ hzero hp).self_of_nhds
  simp only [coefficientProbeSineQuotient, angularSineQuotient, if_neg haxis, he]

/-- The radial order is preserved and the same numerator bound is used
on each angular segment. In particular the normalization costs nothing
where its two axis traces vanish on an open radial region. -/
theorem exists_coefficientProbeSineQuotient_mixed_constant
    (square : Bool) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ReferenceData} {F : PolarPoint → ℝ},
      CoefficientProbeFieldRegularity D F → ∀ {J : Set ℝ}, IsOpen J →
      (∀ r ∈ J, F (r, 0) = 0 ∧ F (r, Real.pi / 2) = 0) →
      ∀ {p : PolarPoint}, p.1 ∈ J → ∀ {M : ℝ}, 0 ≤ M →
        (∀ i j : ℕ, i + j ≤ a + b + sineFactorOrder square → ∀ θ : ℝ,
          |mixedDerivative i j F (p.1, θ)| ≤ M) →
        |mixedDerivative a b (coefficientProbeSineQuotient square F) p| ≤ C * M := by
  obtain ⟨C, hC, hbound⟩ := exists_angularSineQuotient_mixed_constant square a b
  refine ⟨C, hC, ?_⟩
  intro D F hF J hJ hzero p hp M hM hjet
  have hN := coefficientAxisNormalize_fieldRegularity hF
  apply hbound (coefficientAxisNormalize F) hN.1
    (fun c hc r => periodicField_zero_at_doubledSineZeros hN.2.2.1
      (coefficientAxisNormalize_axis_values F) hc r)
    (fun _ c hc r => coefficientProbeField_firstJet_zero_at_doubledSineZeros hN hc r)
    p M hM
  intro i j hij θ
  rw [coefficientAxisNormalize_mixedDerivative_eq hJ hzero
    (p := (p.1, θ)) hp i j]
  exact hjet i j hij θ

end ContinuousFlexibility.Analysis
