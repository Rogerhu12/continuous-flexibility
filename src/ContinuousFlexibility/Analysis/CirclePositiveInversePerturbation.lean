import ContinuousFlexibility.Analysis.CirclePositiveInverseSmoothTame
import ContinuousFlexibility.Analysis.CircleInversePerturbation

/-!
# The inverse displacement on the complete positive-lift domain

The choice-free formula in the supplied circle model is the negative
diagonal of the canonical inverse composition operator. Local lower
derivative bounds identify its decoder with the actual inverse lift;
the resulting smooth tame map uses the whole open positive domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circlePositiveInversePerturbation
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) : S.Space :=
  -circlePositiveInverseComposeLinear hS hT hD hγ travel e e

theorem circlePositiveInversePerturbation_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) (he : e ∈ circlePositiveLiftDomain S) :
    S.decode (circlePositiveInversePerturbation hS hT hD hγ travel e) =
      fun m θ => circleAffineInverse travel e m θ - (θ - travel m) := by
  obtain ⟨a, ha, hb⟩ := circlePositiveLiftDomain_uniform_lower hS hT hD hγ he
  have hlower (m : ℕ) (θ : ℝ) :
      a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ := by
    rw [circleAffineLift_deriv hS]
    exact hb m θ
  have heq : circlePositiveInversePerturbation hS hT hD hγ travel e =
      circleInversePerturbation hS hT hD hγ travel a ha e := by
    unfold circlePositiveInversePerturbation circleInversePerturbation
    rw [circlePositiveInverseComposeLinear_eq_fixed hS hT hD hγ travel a ha e hlower]
  rw [heq]
  exact circleInversePerturbation_decode hS hT hD hγ travel a ha e hlower

theorem smoothTameOn_circlePositiveInversePerturbation
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn S.grading S.grading (circlePositiveLiftDomain S)
      (circlePositiveInversePerturbation hS hT hD hγ travel) := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  exact smoothTameOn_neg_diagonal
    (gradedSeminorm_monotone (fun n => S.level n) S.bond)
    (withSeminorms_graded (fun n => S.level n) S.bond)
    (circlePositiveLiftDomain_isOpen hS hT hD hγ)
    (smoothTameOn_circlePositiveInverseComposeLinear hS hT hD hγ hinterp travel)

end ContinuousFlexibility.Statements
