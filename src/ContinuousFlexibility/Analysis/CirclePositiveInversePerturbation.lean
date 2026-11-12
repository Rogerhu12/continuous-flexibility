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

private theorem positiveInversePerturbation_scalar_identity
    (r t u θ : ℝ) (h : r + t + 1 * u = θ) :
    -u = r - (θ - t) := by
  linarith only [h]

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
  have hdecode := circlePositiveInverseComposeLinear_decode
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel e e he
  funext m θ
  have hneg : S.decode (circlePositiveInversePerturbation hS hT hD hγ travel e) m θ =
      -S.decode e m (circleAffineInverse travel e m θ) :=
    (congrArg (fun f : ℕ → ℝ → ℝ => f m θ)
      (S.decode.map_neg (circlePositiveInverseComposeLinear hS hT hD hγ travel e e))).trans
        (congrArg (fun y : ℝ => -y)
          (congrArg (fun f : ℕ → ℝ → ℝ => f m θ) hdecode))
  exact hneg.trans (positiveInversePerturbation_scalar_identity
    (circleAffineInverse travel e m θ) (travel m)
    (S.decode e m (circleAffineInverse travel e m θ)) θ
    (circleAffineInverse_right
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel e m θ))

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
