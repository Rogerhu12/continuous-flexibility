module

public import ContinuousFlexibility.Analysis.N07aHeightFluxConservation

/-!
# Source compatibility of the actual coefficient operators

The radial and angular flux conservation lemmas apply to the literal
common-height operator and to the positive-weight coefficient perturbation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n07a_scalarCoefficientOperator_Q_zero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a b c : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    S.Q (scalarCoefficientOperatorCLM hD hT hS a b c u) = 0 := by
  have hn := n07a_height_radial_Q_zero hT hS
    (scalarCoefficientNormalCLM hD hT hS a b u)
  have ht := n07a_height_angularSecond_Q_zero hD hT hS
    (scalarCoefficientAngularPrimitiveCLM hD hT hS b c u)
  exact (congrArg S.Q (scalarCoefficientOperatorCLM_apply hD hT hS a b c u)).trans
    ((map_add S.Q _ _).trans ((congrArg₂ (· + ·) hn ht).trans (zero_add 0)))

theorem n07aMixedAngularCLM_Q_zero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ)
    (b c : (S.height γ).Space) (u : ScalarCommonHeight S) :
    S.Q (n07aMixedAngularCLM hD hT hS hγ.le b c u) = 0 := by
  have hb := (physical_height_contDiff_and_flatJets hT hS hγ b).1
  have hc := (physical_height_contDiff_and_flatJets hT hS hγ c).1
  have hu : ContDiff ℝ ∞ (scalarCommonHeightDecode S u) := scalarCommonHeightDecode_contDiff hT hS u
  have hbθ : ContDiff ℝ ∞ (angularPartial ((S.height γ).decode b)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hb.contDiffAt (by simp)
  have hur : ContDiff ℝ ∞ (radialPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_radialPartial hu.contDiffAt (by simp)
  have huθ : ContDiff ℝ ∞ (angularPartial (scalarCommonHeightDecode S u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hu.contDiffAt (by simp)
  have hbper := periodic_angularPartial (((hS.1 γ).2.2.2.1 b).2.2.1)
  have hcper := ((hS.1 γ).2.2.2.1 c).2.2.1
  have huper : Function.Periodic (scalarCommonHeightDecode S u) (0, Real.pi) :=
    scalarCommonHeightDecode_periodic hS u
  have hperiod : Function.Periodic (fun p =>
      angularPartial ((S.height γ).decode b) p * radialPartial (scalarCommonHeightDecode S u) p +
        (S.height γ).decode c p * angularPartial (scalarCommonHeightDecode S u) p)
      (0, Real.pi) := by
    intro p
    simp only [hbper p, hcper p, periodic_radialPartial huper p,
      periodic_angularPartial huper p]
  have hQ : S.Q (n07aMixedAngularCLM hD hT hS hγ.le b c u) =
      physicalSourceIntegral D ((S.height scalarBeta).decode
        (n07aMixedAngularCLM hD hT hS hγ.le b c u)) := by
    exact hS.2.2.2.2.2.2.2.1 _
  exact hQ.trans ((congrArg (physicalSourceIntegral D)
    (n07aMixedAngularCLM_decode hD hT hS hγ b c u)).trans
      (physicalSourceIntegral_angularPartial_eq_zero hD.choose_spec.1.2.1.le
        ((hbθ.mul hur).add (hc.mul huθ)).contDiffOn hperiod))

theorem n07aMixedCoefficientOperator_Q_zero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {γ : ℝ} (hγ : 0 < γ)
    (a b c : (S.height γ).Space) (u : ScalarCommonHeight S) :
    S.Q (n07aMixedCoefficientOperatorCLM hD hT hS hγ.le a b c u) = 0 := by
  have he : n07aMixedCoefficientOperatorCLM hD hT hS hγ.le a b c u =
      SobolevModelData.radialCLM hT (hS.1 scalarBeta)
        (n07aMixedNormalCLM hD hT hS hγ.le a b u) +
        n07aMixedAngularCLM hD hT hS hγ.le b c u := by
    simp only [n07aMixedCoefficientOperatorCLM, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply]
  have hn := n07a_height_radial_Q_zero hT hS
    (n07aMixedNormalCLM hD hT hS hγ.le a b u)
  have ht := n07aMixedAngularCLM_Q_zero hD hT hS hγ b c u
  exact (congrArg S.Q he).trans
    ((map_add S.Q _ _).trans ((congrArg₂ (· + ·) hn ht).trans (zero_add 0)))

end ContinuousFlexibility.Analysis
