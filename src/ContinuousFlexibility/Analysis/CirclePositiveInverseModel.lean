module

public import ContinuousFlexibility.Analysis.CirclePositiveLiftDomain

/-!
# One inverse-composition map on the positive-lift domain

The lower derivative bound is chosen only to realize the inverse in the
given circle model. The decoded operator is always composition with the
same actual invFun. Thus different local lower bounds give the same
operator, which permits their genuine smooth tame towers to be glued.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circlePositiveInverseComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) : S.Space →ₗ[ℝ] S.Space := by
  classical
  exact if he : e ∈ circlePositiveLiftDomain S then
    let h := circlePositiveLiftDomain_uniform_lower hS hT hD hγ he
    circleInverseComposeLinear hS hT hD hγ travel h.choose h.choose_spec.1 e
  else 0

theorem circlePositiveInverseComposeLinear_decode
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e u : S.Space)
    (he : e ∈ circlePositiveLiftDomain S) :
    S.decode (circlePositiveInverseComposeLinear hS hT hD hγ travel e u) =
      fun m θ => S.decode u m (circleAffineInverse travel e m θ) := by
  classical
  simp only [circlePositiveInverseComposeLinear, dif_pos he]
  apply circleInverseComposeLinear_decode
  intro m θ
  rw [circleAffineLift_deriv hS]
  exact (circlePositiveLiftDomain_uniform_lower hS hT hD hγ he).choose_spec.2 m θ

theorem circlePositiveInverseComposeLinear_eq_fixed
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (e : S.Space)
    (hlower : ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    circlePositiveInverseComposeLinear hS hT hD hγ travel e =
      circleInverseComposeLinear hS hT hD hγ travel a ha e := by
  have he : e ∈ circlePositiveLiftDomain S :=
    (circlePositiveLiftDomain_iff hS travel e).mpr (fun m θ => ha.trans_le (hlower m θ))
  apply LinearMap.ext
  intro u
  apply hS.2.2.2.2.2.1
  exact (circlePositiveInverseComposeLinear_decode hS hT hD hγ travel e u he).trans
    (circleInverseComposeLinear_decode hS hT hD hγ travel a ha e u hlower).symm

theorem circleAffineInverse_eq_of_leftInverse
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e : S.Space) (g : ℕ → ℝ → ℝ)
    (hleft : ∀ m θ, g m (circleAffineLift travel (S.decode e) 1 m θ) = θ)
    (m : ℕ) (θ : ℝ) : circleAffineInverse travel e m θ = g m θ := by
  exact (hleft m (circleAffineInverse travel e m θ)).symm.trans
    (congrArg (g m) (circleAffineInverse_right hS hT hD hγ travel e m θ))

theorem circlePositiveInverseComposeLinear_decode_of_leftInverse
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (travel : ℕ → ℝ) (e u : S.Space)
    (he : e ∈ circlePositiveLiftDomain S) (g : ℕ → ℝ → ℝ)
    (hleft : ∀ m θ, g m (circleAffineLift travel (S.decode e) 1 m θ) = θ)
    (m : ℕ) (θ : ℝ) :
    S.decode (circlePositiveInverseComposeLinear hS hT hD hγ travel e u) m θ =
      S.decode u m (g m θ) := by
  rw [circlePositiveInverseComposeLinear_decode hS hT hD hγ travel e u he]
  exact congrArg (S.decode u m)
    (circleAffineInverse_eq_of_leftInverse hS hT hD hγ travel e g hleft m θ)

end ContinuousFlexibility.Statements
