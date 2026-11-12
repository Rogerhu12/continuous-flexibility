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

private theorem circlePositiveInversePerturbation_decode_of_linear_eq
    {E V : Type*} [AddCommGroup E] [Module ℝ E]
    (decode : E → V) (A B : E →ₗ[ℝ] E) (e : E)
    (hAB : A = B) {v : V} (hB : decode (-B e) = v) :
    decode (-A e) = v := by
  exact (congrArg (fun L : E →ₗ[ℝ] E => decode (-L e)) hAB).trans hB

theorem circlePositiveInversePerturbation_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) (he : e ∈ circlePositiveLiftDomain S) :
    S.decode (circlePositiveInversePerturbation hS hT hD hγ travel e) =
      fun m θ => circleAffineInverse travel e m θ - (θ - travel m) := by
  obtain ⟨a, ha, hb⟩ := circlePositiveLiftDomain_uniform_lower
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ he
  have hlower (m : ℕ) (θ : ℝ) :
      a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ :=
    (hb m θ).trans_eq
      (circleAffineLift_deriv (T := T) (γ := γ) (S := S) hS travel e m θ).symm
  exact circlePositiveInversePerturbation_decode_of_linear_eq
    (E := S.Space) (V := ℕ → ℝ → ℝ) (fun u : S.Space => S.decode u)
    (circlePositiveInverseComposeLinear hS hT hD hγ travel e)
    (circleInverseComposeLinear hS hT hD hγ travel a ha e) e
    (circlePositiveInverseComposeLinear_eq_fixed
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel a ha e hlower)
    (circleInversePerturbation_decode
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel a ha e hlower)

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
