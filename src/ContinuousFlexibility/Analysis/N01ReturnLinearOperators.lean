import ContinuousFlexibility.Analysis.N01UniformReturnMargins
import ContinuousFlexibility.Analysis.CircleReturnWeightedInverse
import ContinuousFlexibility.Analysis.CircleCompositionModel

/-!
# The actual N01 return operators in the supplied circle space

Optical normalization and the N01 variation bounds give one uniform
sample-weight bound for all small divisors.  The scalar Fourier inverse
therefore realizes an operator on the original physical circle model with
four levels of loss: three angular levels and one sample-weight level.
Both inverse identities retain the required even/zero-mean and odd sectors.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped NNReal

theorem N01Properties.returnLinearOperators
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ L : CircleSpace S →L[ℝ] CircleSpace S,
      ∃ J : CircleSpace S →ₗ[ℝ] CircleSpace S,
        (∀ v m θ, (S.circle (3 / 4 : ℝ)).decode (L v) m θ =
          circleRotationDifference S C v m θ) ∧
        (∀ g, IsEvenZeroMeanCircle S g → L (J g) = g ∧ IsOddCircle S (J g)) ∧
        (∀ v, IsOddCircle S v → J (L v) = v) ∧
        IsTameLinear (S.circle (3 / 4 : ℝ)).grading
          (S.circle (3 / 4 : ℝ)).grading J 4 0 := by
  let SC : CircleModelData := S.circle (3 / 4 : ℝ)
  have hCircle : IsCircleModel T (3 / 4 : ℝ) SC := hS.2.1 _
  have hM : ∀ m, 0 ≤ T.M (T.sample m) :=
    fun m => (material_circle_sample_weights_pos hT hN.1.1).1 m |>.le
  have hH : ∀ m, 0 ≤ T.H (T.sample m) :=
    fun m => (material_circle_sample_weights_pos hT hN.1.1).2 m |>.le
  obtain ⟨A, hA, c, hc, hbound, hdiv⟩ := hN.uniform_returnMargin_family hS hT
  have hbound' : ∀ m, (c m)⁻¹ ≤ A * T.M (T.sample m) ^ (1 : ℕ) := by
    simpa only [pow_one] using hbound
  let L : CircleSpace S →L[ℝ] CircleSpace S :=
    circleReturnContinuousLinear hCircle C.travel
  let J : CircleSpace S →ₗ[ℝ] CircleSpace S :=
    circleReturnInverseLinear hCircle C.travel c hc hdiv 1 hA.le hbound' hM hH
  have hL (v : CircleSpace S) : L v = circleReturnLinear hCircle C.travel v :=
    IsTameLinear.toContinuousLinearMap_apply (circleReturnLinear_tame hCircle C.travel)
      (withSeminorms_graded (fun i => SC.level i) SC.bond)
      (withSeminorms_graded (fun i => SC.level i) SC.bond)
      (gradedSeminorm_monotone (fun i => SC.level i) SC.bond) v
  refine ⟨L, J, ?_, ?_, ?_, ?_⟩
  · intro v m θ
    simpa only [circleRotationDifference, evenPart, circleReturnShift, circleReturnEven] using
      circleReturnContinuousLinear_decode hCircle C.travel v m θ
  · intro g hg
    constructor
    · rw [hL]
      exact circleReturnInverseLinear_right_inverse hCircle C.travel c hc hdiv 1
        hA.le hbound' hM hH g (fun m => (hg m).1) (fun m => (hg m).2)
    · intro m θ
      exact circleReturnInverseLinear_odd hCircle C.travel c hc hdiv 1
        hA.le hbound' hM hH g m θ
  · intro v hv
    rw [hL]
    exact circleReturnInverseLinear_left_inverse hCircle C.travel c hc hdiv 1
      hA.le hbound' hM hH v hv
  · exact circleReturnInverseLinear_tame hCircle C.travel c hc hdiv 1
      hA.le hbound' hM hH

end ContinuousFlexibility.Statements
