module

public import ContinuousFlexibility.Analysis.N07aMixedCoefficientOperator
public import ContinuousFlexibility.Scalar.WeightedErrorConservation
public import ContinuousFlexibility.Scalar.WeightedLinearConservation

/-!
# Actual source compatibility of the forward operator

The radial flux is a positive-weight height and vanishes at both ends.
The angular flux is periodic. These are the boundary identities used in
the physical integral; no projection onto the source kernel is inserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n07a_height_radial_Q_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) :
    S.Q (SobolevModelData.radialCLM hT (hS.1 scalarBeta) u) = 0 := by
  have hu := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  have hz (θ : ℝ) : (S.height scalarBeta).decode u (D.b, θ) =
      (S.height scalarBeta).decode u (D.a, θ) := by
    rw [((hS.1 scalarBeta).2.2.2.1 u).2.2.2.1 (D.b, θ)
        (fun hp => (lt_irrefl D.b) hp.1.2),
      ((hS.1 scalarBeta).2.2.2.1 u).2.2.2.1 (D.a, θ)
        (fun hp => (lt_irrefl D.a) hp.1.1)]
  have hi := integral_exteriorCoefficient_eq_zero
    (α := ⟨fun _ => 0, (S.height scalarBeta).decode u⟩)
    (a := D.a) (b := D.b) (c := 0) (d := Real.pi)
    (fun _ _ => contDiffAt_const)
    (fun _ _ => hu.contDiffAt.of_le (by simp))
    (fun _ _ => rfl) (fun θ _ => hz θ)
  have hzero : scalarAnnularIntegral D (radialPartial ((S.height scalarBeta).decode u)) = 0 := by
    simpa only [scalarAnnularIntegral, exteriorCoefficient, angularPartial_const, sub_zero]
      using hi
  have hQ : S.Q (SobolevModelData.radialCLM hT (hS.1 scalarBeta) u) =
      physicalSourceIntegral D ((S.height scalarBeta).decode
        (SobolevModelData.radialCLM hT (hS.1 scalarBeta) u)) := by
    exact hS.2.2.2.2.2.2.2.1 _
  rw [hQ, SobolevModelData.decode_radialCLM,
    physicalSourceIntegral_eq_scaled_annularIntegral, hzero, mul_zero]

theorem n07a_height_angularSecond_Q_zero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    S.Q (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta) u) = 0 := by
  have hu := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  have hθ : ContDiff ℝ ∞ (angularPartial ((S.height scalarBeta).decode u)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial hu.contDiffAt (by simp)
  have hp := periodic_angularPartial (((hS.1 scalarBeta).2.2.2.1 u).2.2.1)
  have hQ : S.Q (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta) u) =
      physicalSourceIntegral D ((S.height scalarBeta).decode
        (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta) u)) := by
    exact hS.2.2.2.2.2.2.2.1 _
  rw [hQ, SobolevModelData.decode_angularSecondCLM]
  exact physicalSourceIntegral_angularPartial_eq_zero
    hD.choose_spec.1.2.1.le hθ.contDiffOn hp

end ContinuousFlexibility.Analysis
