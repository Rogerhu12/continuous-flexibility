import ContinuousFlexibility.Analysis.N07aMixedCoefficientOperator
import ContinuousFlexibility.Scalar.WeightedScalarOperator

/-!
# Decoding the reference operator plus the actual mixed-weight perturbation

This identity only uses three arbitrary physical height coefficients.
The nonlinear coefficient towers enter later, when those three inputs
are specialized to the N01 fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n07a_symmetricDivergence_coeff_congr
    {A B C A' B' C' u : PolarPoint → ℝ} {p : PolarPoint}
    (hA : A =ᶠ[𝓝 p] A') (hB : B =ᶠ[𝓝 p] B') (hC : C =ᶠ[𝓝 p] C') :
    symmetricDivergence A B C u p = symmetricDivergence A' B' C' u p := by
  have hn : symmetricNormalFlux A B u =ᶠ[𝓝 p] symmetricNormalFlux A' B' u := by
    filter_upwards [hA, hB] with q hqa hqb
    simp only [symmetricNormalFlux, hqa, hqb]
  have ht : symmetricAngularFlux B C u =ᶠ[𝓝 p] symmetricAngularFlux B' C' u := by
    filter_upwards [hB, hC] with q hqb hqc
    simp only [symmetricAngularFlux, hqb, hqc]
  exact congrArg₂ (· + ·)
    (congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hn.fderiv_eq)
    (congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) ht.fderiv_eq)

private theorem n07a_symmetricDivergence_add
    {A B C A' B' C' u : PolarPoint → ℝ} {p : PolarPoint}
    (hA : ContDiffAt ℝ ∞ A p) (hB : ContDiffAt ℝ ∞ B p)
    (hC : ContDiffAt ℝ ∞ C p) (hA' : ContDiffAt ℝ ∞ A' p)
    (hB' : ContDiffAt ℝ ∞ B' p) (hC' : ContDiffAt ℝ ∞ C' p)
    (hu : ContDiffAt ℝ ∞ u p) :
    symmetricDivergence (fun q => A q + A' q) (fun q => B q + B' q)
      (fun q => C q + C' q) u p =
      symmetricDivergence A B C u p + symmetricDivergence A' B' C' u p := by
  have hn : symmetricNormalFlux (fun q => A q + A' q) (fun q => B q + B' q) u =
      fun q => symmetricNormalFlux A B u q + symmetricNormalFlux A' B' u q := by
    funext q
    simp only [symmetricNormalFlux]
    ring
  have ht : symmetricAngularFlux (fun q => B q + B' q) (fun q => C q + C' q) u =
      fun q => symmetricAngularFlux B C u q + symmetricAngularFlux B' C' u q := by
    funext q
    simp only [symmetricAngularFlux]
    ring
  unfold symmetricDivergence
  rw [hn, ht,
    radialPartial_add ((contDiffAt_symmetricNormalFlux hA hB hu).differentiableAt (by simp))
      ((contDiffAt_symmetricNormalFlux hA' hB' hu).differentiableAt (by simp)),
    angularPartial_add ((contDiffAt_symmetricAngularFlux hB hC hu).differentiableAt (by simp))
      ((contDiffAt_symmetricAngularFlux hB' hC' hu).differentiableAt (by simp))]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n07a_reference_add_mixed_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ)
    (a b c : (S.height γ).Space) (u : ScalarCommonHeight S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height scalarBeta).decode
        (scalarCoefficientOperatorCLM hD hT hS 0 0 0 u +
          n07aMixedCoefficientOperatorCLM hD hT hS hγ.le a b c u) p =
      symmetricDivergence
        (fun q => D.w q.1 + (S.height γ).decode a q)
        (fun q => 0 + angularPartial ((S.height γ).decode b) q)
        (fun q => deriv D.w q.1 / q.1 + (S.height γ).decode c q)
        (scalarCommonHeightDecode S u) p := by
  have ha := (physical_height_contDiff_and_flatJets hT hS hγ a).1
  have hb : ContDiff ℝ ∞ (angularPartial ((S.height γ).decode b)) := by
    have h := (physical_height_contDiff_and_flatJets hT hS hγ b).1
    exact contDiff_iff_contDiffAt.mpr fun q =>
      contDiffAt_angularPartial h.contDiffAt (by simp)
  have hc := (physical_height_contDiff_and_flatJets hT hS hγ c).1
  have hw : ContDiff ℝ ∞ D.w := hD.choose_spec.1.2.2.1.1
  have hdw : ContDiff ℝ ∞ (deriv D.w) := (contDiff_infty_iff_deriv.mp hw).2
  have hr : p.1 ≠ 0 := (hD.choose_spec.1.1.trans hp.1.1).ne'
  have hadd := n07a_symmetricDivergence_add (p := p)
    (A := fun q => D.w q.1) (B := fun _ => (0 : ℝ))
    (C := fun q => deriv D.w q.1 / q.1)
    (A' := (S.height γ).decode a)
    (B' := angularPartial ((S.height γ).decode b))
    (C' := (S.height γ).decode c)
    (u := scalarCommonHeightDecode S u)
    (hw.comp contDiff_fst).contDiffAt contDiffAt_const
    ((hdw.comp contDiff_fst).contDiffAt.div contDiffAt_fst hr)
    ha.contDiffAt hb.contDiffAt hc.contDiffAt
    (scalarCommonHeightDecode_contDiff hT hS u).contDiffAt
  have hθ0 : angularPartial (0 : PolarPoint → ℝ) = fun _ => 0 := by
    funext q
    exact angularPartial_const 0
  have href : (S.height scalarBeta).decode
      (scalarCoefficientOperatorCLM hD hT hS 0 0 0 u) p =
      symmetricDivergence (fun q => D.w q.1) (fun _ => 0)
        (fun q => deriv D.w q.1 / q.1) (scalarCommonHeightDecode S u) p := by
    simpa only [map_zero, Pi.zero_apply, add_zero, hθ0] using
      congrFun (decode_scalarCoefficientOperatorCLM hD hT hS 0 0 0 u) p
  have hdelta := congrFun (n07aMixedCoefficientOperatorCLM_decode hD hT hS hγ a b c u) p
  exact (congrFun (map_add (S.height scalarBeta).decode _ _) p).trans
    ((congrArg₂ (· + ·) href hdelta).trans hadd.symm)


end ContinuousFlexibility.Analysis
